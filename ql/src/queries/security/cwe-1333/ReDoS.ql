/**
 * @name Inefficient regular expression
 * @description A regular expression that requires exponential time to match certain inputs
 *              can be a performance bottleneck, and may be vulnerable to denial-of-service
 *              attacks.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @id rb/redos
 * @tags security
 *       external/cwe/cwe-1333
 *       external/cwe/cwe-730
 *       external/cwe/cwe-400
 */

import codeql_ruby.regexp.ExponentialBackTracking

from RegExpTerm t, string pump, State s, string prefixMsg
where hasReDoSResult(t, pump, s, prefixMsg)
select t,
  "This part of the regular expression may cause exponential backtracking on strings " + prefixMsg +
    "containing many repetitions of '" + pump + "'."