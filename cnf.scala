package cnf

import stainless.collection.List
import stainless.lang._
import scala.language.postfixOps
import stainless.math.wrapping
import stainless.proof._ 
import utils._
import formula._
import stainless.annotation._

package object cnf {
    def ok = {
        assert(true)

        def var1 = Var(1);
        def var2 = Not(Var(1));
        def var3 = And(Var(1), Var(2));
    }

    // def applyRule1
    
    def applyRule1(f : FormulaT, orsAboveLeft : BigInt, andsAboveLef : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[DImplies])
        // require(orsAboveLeft >= 0)
        // require(andsAboveLeft >= 0)
        
        val DImplies(f1, f2) = f
        val result = And(Implies(f1, f2), Implies(f2, f1))

        assert(countDImplies(And(Implies(f1, f2), Implies(f2, f1))) ==
            countDImplies(Implies(f1, f2)) + countDImplies(Implies(f2, f1)))

        assert(countDImplies(And(Implies(f1, f2), Implies(f2, f1))) ==
            2 * (countDImplies(f1) + countDImplies(f2)))

        mult2_upper(countDImplies(f1) + countDImplies(f2))
        result

    } ensuring(res =>
        (validFormulaT(res))
        &&
        (countDImplies(res) < countDImplies(f))
    )


    /////////////////////
    ///// FUNCTIONS /////
    /////////////////////

    @induct
    def countDImplies(f: FormulaT) : BigInt = {

        f match {
            case Var(v)           => BigInt(0)
            case Not(f1)          => countDImplies(f1)
            case Or(f1, f2)       => countDImplies(f1) + countDImplies(f2)
            case And(f1, f2)      => countDImplies(f1) + countDImplies(f2)
            case Implies(f1, f2)  => countDImplies(f1) + countDImplies(f2)
            case DImplies(f1, f2) => BigInt(1) + pow(2, countDImplies(f1) + countDImplies(f2))
        }
    } ensuring(
        res => res >= 0
    )

    @induct
    def mult2_upper(x : BigInt) : Boolean = {

        require(x >= BigInt(0))
        BigInt(2) * x < BigInt(1) + pow(BigInt(2), x)
    }.holds
}