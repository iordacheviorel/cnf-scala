package cnf

import stainless.collection.List
import stainless.lang._
import scala.language.postfixOps
import stainless.math.wrapping
import stainless.proof._ 
import utils._
import stainless.annotation._

// sealed trait FormulaT
sealed trait FormulaT
case class Var(v: BigInt) extends FormulaT
case class Not(f1: FormulaT) extends FormulaT
case class Or(f1: FormulaT, f2: FormulaT) extends FormulaT
case class And(f1: FormulaT, f2: FormulaT) extends FormulaT
case class Implies(f1: FormulaT, f2: FormulaT) extends FormulaT
case class DImplies(f1: FormulaT, f2: FormulaT) extends FormulaT

  package object formula {
    def ok = {
        assert(true)

        def var1 = Var(1);
        def var2 = Not(Var(1));
        def var3 = And(Var(1), Var(2));
    }

    // DONE
    @induct
    def maxVar(f: FormulaT) : BigInt = {
        require(validFormulaT(f))

        f match {
            case Var(v)           => v + 1
            case Not(f1)          => 
                val n1 = maxVar(f1)
                maxVar(f1)
            case Or(f1, f2)       =>
                val v1 = maxVar(f1)
                val v2 = maxVar(f2)
                val n = utils.max(v1, v2)
                variablesUpToMonotone(f1, v1, n)
                variablesUpToMonotone(f2, v2, n)
                n
            case And(f1, f2)      => 
                val v1 = maxVar(f1)
                val v2 = maxVar(f2)
                val n = utils.max(v1, v2)
                variablesUpToMonotone(f1, v1, n)
                variablesUpToMonotone(f2, v2, n)
                n
            case Implies(f1, f2)  => 
                val v1 = maxVar(f1)
                val v2 = maxVar(f2)
                val n = utils.max(v1, v2)
                variablesUpToMonotone(f1, v1, n)
                variablesUpToMonotone(f2, v2, n)
                n
            case DImplies(f1, f2) => 
                val v1 = maxVar(f1)
                val v2 = maxVar(f2)
                val n = utils.max(v1, v2)
                variablesUpToMonotone(f1, v1, n)
                variablesUpToMonotone(f2, v2, n)
                n
        }
    } ensuring(res => 
        (variablesUpTo(f, res)) &&
        (res >= 0)
    )

    // DONE
    @induct
    def variablesUpTo(f: FormulaT, n: BigInt):  Boolean = { 

        f match {

            case Var(v) => 0 <= v && v < n
            case Not(f1) => variablesUpTo(f1, n)
            case Or(f1, f2) => variablesUpTo(f1, n) && variablesUpTo(f2, n)
            case And(f1, f2) => variablesUpTo(f1, n) && variablesUpTo(f2, n)
            case Implies(f1, f2) => variablesUpTo(f1, n) && variablesUpTo(f2, n)
            case DImplies(f1, f2) => variablesUpTo(f1, n) && variablesUpTo(f2, n)
    }} ensuring (res => res == false || validFormulaT(f))

    // DONE
    def variablesUpToMaxVar(f: FormulaT, n :BigInt) : Boolean = {

        require(variablesUpTo(f, n))
        validFormulaT(f)
        n >= maxVar(f)
    }

    // DONE
    @induct
    def variablesUpToMonotone(f : FormulaT, n1 : BigInt, n2 : BigInt) : Boolean = {

        require(variablesUpTo(f, n1) && (n1 <= n2))
        
        variablesUpTo(f, n2)
    }.holds

    // DONE
    def variablesUpToVar(v : BigInt) : Boolean = {

        require(v >= 0)
        variablesUpTo(Var(v), v + 1) 
    }.holds

    // DONE
    @induct
    def validFormulaT(f: FormulaT):  Boolean = {
    f match {

        case Var(v) => 0 <= v
        case Not(f1) => validFormulaT(f1)
        case Or(f1, f2) => validFormulaT(f1) && validFormulaT(f2)
        case And(f1, f2) => validFormulaT(f1) && validFormulaT(f2)
        case Implies(f1, f2) => validFormulaT(f1) && validFormulaT(f2)
        case DImplies(f1, f2) => validFormulaT(f1) && validFormulaT(f2)
    }}

    // CNF
    // 
    // def truthValue
    @induct
    def truthValue(f: FormulaT, assignment: List[Boolean]) : Boolean = {
        require(validFormulaT(f))
        require(variablesUpTo(f, assignment.size))

        f match {
            case And(f1,f2) =>
                truthValue(f1, assignment) &&
                truthValue(f2, assignment)
            case Var(v) =>
                assignment.apply(v)
            case Or(f1,f2) =>
                truthValue(f1, assignment) ||
                truthValue(f2, assignment)
            case Not(f1) =>
                !truthValue(f1, assignment)
            case Implies(f1,f2) =>
                !truthValue(f1, assignment) ||
                truthValue(f2, assignment)
            case DImplies(f1,f2) =>
                truthValue(f1, assignment) ==
                truthValue(f2, assignment)
        }
    }

    // CNF
    // def equivalent
    // def equivalent(f1 : FormulaT, f2 : FormulaT) : Boolean = {

    //     require(validFormulaT(f1))
    //     require(validFormulaT(f2))

        
    // }

    // @induct
    // def assignments(n : BigInt) : List[List[BigInt]] = {

    //     if n == 1


    // }

    // TSEITIN ONLY
    // def assignmentRelevant

    // CNF - equivalentTrans (in formula.dfy)
    // def seqFalse

    // CNF
    // def equivalentTrans

    // pretty print

    // def equivalent(f1 : FormulaT, f2 : FormulaT) : Boolean = {

    //     require (validFormulaT(f1))
    //     require (validFormulaT(f2))

    //     forall((tau : List[Boolean]) => variablesUpTo(f1, tau.size) &&
    //         variablesUpTo(f2, tau.size) ==>
    //         truthValue(f1, tau) == truthValue(f2, tau))

    //     // assert (forall((i : List[BigInt]) => i.size == i.size))
    // }.holds

}