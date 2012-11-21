package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import rules._

object Rules {
  def all = Set[Synthesizer => Rule](
    new Unification.DecompTrivialClash(_),
    new Unification.OccursCheck(_),
    new ADTDual(_),
    new OnePoint(_),
    new Ground(_),
    new CaseSplit(_),
    new UnusedInput(_),
    new UnconstrainedOutput(_),
    new OptimisticGround(_),
    new EqualitySplit(_),
    new CEGIS(_),
    new Assert(_),
    new ADTSplit(_),
    new IntegerEquation(_),
    new IntegerInequalities(_)
  )
}

case class RuleResult(alternatives: Traversable[RuleApplication])
object RuleInapplicable extends RuleResult(List())

abstract class RuleApplication(val subProblemsCount: Int,
                               val onSuccess: List[Solution] => Solution) {

  def apply(): RuleApplicationResult
}

abstract class RuleImmediateApplication extends RuleApplication(0, s => Solution.simplest)

sealed abstract class RuleApplicationResult
case class RuleSuccess(solution: Solution) extends RuleApplicationResult
case class RuleDecomposed(sub: List[Problem], onSuccess: List[Solution] => Solution) extends RuleApplicationResult
case object RuleApplicationImpossible extends RuleApplicationResult

object RuleFastApplication {
  def apply(sub: List[Problem], onSuccess: List[Solution] => Solution) = {
    new RuleApplication(sub.size, onSuccess) {
      def apply() = RuleDecomposed(sub, onSuccess)
    }
  }
}

object RuleFastInapplicable {
  def apply() = {
    RuleResult(List(new RuleApplication(0, ls => Solution.simplest) {
      def apply() = RuleApplicationImpossible
    }))
  }
}

object RuleFastStep {
  def apply(sub: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleResult(List(RuleFastApplication(sub, onSuccess)))
  }
}

object RuleFastSuccess {
  def apply(solution: Solution) = {
    RuleResult(List(new RuleApplication(0, ls => solution) {
      def apply() = RuleSuccess(solution)
    }))
  }
}

abstract class Rule(val name: String, val synth: Synthesizer, val priority: Priority) {
  def attemptToApplyOn(problem: Problem): RuleResult

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Solution = {
    case List(s) => Solution(s.pre, s.defs, s.term)
    case _ => Solution.none
  }

  override def toString = "R: "+name
}
