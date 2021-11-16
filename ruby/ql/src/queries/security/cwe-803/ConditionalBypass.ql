/**
 * @name User-controlled bypass of security check
 * @description Conditions controlled by the user are not suited for making security-related decisions.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 7.8
 * @precision medium
 * @id rb/user-controlled-bypass
 * @tags security
 *       external/cwe/cwe-807
 *       external/cwe/cwe-290
 */

import ruby
import codeql.ruby.security.SensitiveActions
import codeql.ruby.DataFlow
import codeql.ruby.dataflow.internal.DataFlowPublic
import codeql.ruby.dataflow.RemoteFlowSources
import codeql.ruby.security.ConditionalBypassQuery
import DataFlow::PathGraph

/**
 * Holds if the value of `nd` flows into `guard`.
 */
predicate flowsToGuardExpr(DataFlow::Node nd, SensitiveActionGuardConditional guard) {
  nd = guard
  or
  exists(DataFlow::Node succ | localFlowStep(nd, succ) | flowsToGuardExpr(succ, guard))
}

/**
 * A comparison that guards a sensitive action, e.g. the comparison in:
 * `var ok = x == y; if (ok) login()`.
 */
class SensitiveActionGuardComparison extends ComparisonOperation {
  SensitiveActionGuardConditional guard;

  SensitiveActionGuardComparison() {
    exists(DataFlow::Node node | this = node.asExpr().getExpr() | flowsToGuardExpr(node, guard))
  }

  /**
   * Gets the guard that uses this comparison.
   */
  SensitiveActionGuardConditional getGuard() { result = guard }
}

/**
 * An intermediary sink to enable reuse of the taint configuration.
 * This sink should not be presented to the client of this query.
 */
class SensitiveActionGuardComparisonOperand extends Sink {
  SensitiveActionGuardComparison comparison;

  SensitiveActionGuardComparisonOperand() { this.asExpr().getExpr() = comparison.getAnOperand() }

  override SensitiveAction getAction() { result = comparison.getGuard().getAction() }
}

/**
 * Holds if `sink` guards `action`, and `source` taints `sink`.
 *
 * If flow from `source` taints `sink`, then an attacker can
 * control if `action` should be executed or not.
 */
predicate isTaintedGuardForSensitiveAction(
  DataFlow::PathNode sink, DataFlow::PathNode source, SensitiveAction action
) {
  action = sink.getNode().(Sink).getAction() and
  // exclude the intermediary sink
  not sink.getNode() instanceof SensitiveActionGuardComparisonOperand and
  exists(Configuration cfg |
    // ordinary taint tracking to a guard
    cfg.hasFlowPath(source, sink)
    or
    // taint tracking to both operands of a guard comparison
    exists(
      SensitiveActionGuardComparison cmp, DataFlow::PathNode lSource, DataFlow::PathNode rSource,
      DataFlow::PathNode lSink, DataFlow::PathNode rSink
    |
      sink.getNode() = cmp.getGuard() and
      cfg.hasFlowPath(lSource, lSink) and
      lSink.getNode().asExpr().getExpr() = cmp.getLeftOperand() and
      cfg.hasFlowPath(rSource, rSink) and
      rSink.getNode().asExpr().getExpr() = cmp.getRightOperand()
    |
      source = lSource or
      source = rSource
    )
  )
}

from DataFlow::PathNode source, DataFlow::PathNode sink, SensitiveAction action
where isTaintedGuardForSensitiveAction(sink, source, action)
select sink.getNode(), source, sink, "This condition guards a sensitive $@, but $@ controls it.",
  action, "action", source.getNode(), "a user-provided value"
