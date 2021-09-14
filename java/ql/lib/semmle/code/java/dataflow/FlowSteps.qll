/**
 * Provides classes representing various flow steps for taint tracking.
 */

private import java
private import semmle.code.java.dataflow.DataFlow

/**
 * A module importing the frameworks that implement additional flow steps,
 * ensuring that they are visible to the taint tracking library.
 */
private module Frameworks {
  private import semmle.code.java.frameworks.jackson.JacksonSerializability
  private import semmle.code.java.frameworks.android.Intent
  private import semmle.code.java.frameworks.android.SQLite
  private import semmle.code.java.frameworks.Guice
  private import semmle.code.java.frameworks.Protobuf
  private import semmle.code.java.frameworks.guava.Guava
  private import semmle.code.java.frameworks.apache.Lang
  private import semmle.code.java.frameworks.ApacheHttp
}

/**
 * A method that returns the exact value of one of its parameters or the qualifier.
 *
 * Extend this class and override `returnsValue` to add additional value-preserving steps through a
 * method that should be added to the basic local flow step relation.
 *
 * These steps will be visible for all global data-flow purposes, as well as via
 * `DataFlow::Node.getASuccessor` and other related functions exposing intraprocedural dataflow.
 */
abstract class ValuePreservingMethod extends Method {
  /**
   * Holds if this method returns precisely the value passed into argument `arg`.
   * `arg` is a parameter index, or is -1 to indicate the qualifier.
   */
  abstract predicate returnsValue(int arg);
}

/**
 * A method that returns the exact value of its qualifier (e.g., `return this;`)
 *
 * Extend this class to add additional value-preserving steps from qualifier to return value through a
 * method that should be added to the basic local flow step relation.
 *
 * These steps will be visible for all global data-flow purposes, as well as via
 * `DataFlow::Node.getASuccessor` and other related functions exposing intraprocedural dataflow.
 */
abstract class FluentMethod extends ValuePreservingMethod {
  override predicate returnsValue(int arg) { arg = -1 }
}

/**
 * A unit class for adding additional taint steps.
 *
 * Extend this class to add additional taint steps that should apply to all
 * taint configurations.
 */
class AdditionalTaintStep extends Unit {
  /**
   * Holds if the step from `node1` to `node2` should be considered a taint
   * step for all configurations.
   */
  abstract predicate step(DataFlow::Node node1, DataFlow::Node node2);
}

/**
 * A method or constructor that preserves taint.
 *
 * Extend this class and override at least one of `returnsTaintFrom` or `transfersTaint`
 * to add additional taint steps through a method that should apply to all taint configurations.
 */
abstract class TaintPreservingCallable extends Callable {
  /**
   * Holds if this callable returns tainted data when `arg` tainted.
   * `arg` is a parameter index, or is -1 to indicate the qualifier.
   */
  predicate returnsTaintFrom(int arg) { none() }

  /**
   * Holds if this callable writes tainted data to `sink` when `src` is tainted.
   * `src` and `sink` are parameter indices, or -1 to indicate the qualifier.
   */
  predicate transfersTaint(int src, int sink) { none() }
}

private class NumberTaintPreservingCallable extends TaintPreservingCallable {
  int argument;

  NumberTaintPreservingCallable() {
    this.getDeclaringType().getASupertype*().hasQualifiedName("java.lang", "Number") and
    (
      this instanceof Constructor and
      argument = 0
      or
      this.getName().matches(["to%String", "toByteArray", "%Value"]) and
      argument = -1
      or
      this.getName().matches(["parse%", "valueOf%", "to%String", "decode"]) and
      argument = 0
    )
  }

  override predicate returnsTaintFrom(int arg) { arg = argument }
}