/**
 * Provides classes and predicates for identifying sensitive data and methods for security.
 *
 * 'Sensitive' data in general is anything that should not be sent around in unencrypted form. This
 * library tries to guess where sensitive data may either be stored in a variable or produced by a
 * method.
 *
 * In addition, there are methods that ought not to be executed or not in a fashion that the user
 * can control. This includes authorization methods such as logins, and sending of data, etc.
 */

import codeql.ruby.AST
import codeql.ruby.DataFlow

/**
 * A sensitive action, such as transfer of sensitive data.
 */
abstract class SensitiveAction extends DataFlow::Node { }

/** Holds if the return value from call `c` is ignored. */
private predicate callWithIgnoredReturnValue(Call c) {
  // If the call is a top-level statement within a statement sequence, its
  // return value (if any) is unused. Unless, however, it's the last statement,
  // in which case it is evaluated as the overall value of the sequence.
  exists(StmtSequence s, int i |
    c = s.getStmt(i) and
    exists(s.getStmt(i + 1))
  ) and
  not c instanceof YieldCall and
  // Ignore statements in ERB output directives, which are evaluated.
  not exists(ErbOutputDirective d | d.getAChildStmt() = c)
}

predicate cljdkasldjaslkd(AuthorizationCall c, boolean b) {
  if exists(ErbOutputDirective d | d.getAChildStmt() = c.asExpr().getExpr())
  then b = true
  else b = false
}

/** A call that may perform authorization. */
class AuthorizationCall extends SensitiveAction, DataFlow::CallNode {
  AuthorizationCall() {
    exists(MethodCall c, string s |
      c = this.asExpr().getExpr() and
      s = c.getMethodName() // name contains `login` or `auth`, but not as part of `loginfo` or `unauth`;
    |
      // also exclude `author`
      s.regexpMatch("(?i).*(login(?!fo)|(?<!un)auth(?!or\\b)|verify).*") and
      // but it does not start with `get` or `set`
      not s.regexpMatch("(?i)(get|set).*") and
      // Setter calls are unlikely to be sensitive actions.
      not c instanceof SetterMethodCall and
      // Only consider calls that have no return value (or ignore it) to be
      // actions. Otherwise, we'd get a lot of noisy results from getter
      // methods or other methods that are not actions.
      callWithIgnoredReturnValue(c)
    )
  }
}
