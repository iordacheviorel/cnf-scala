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
    
    def applyRule1(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[DImplies])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
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
        && (weightOfAnds(res) <= weightOfAnds(f))
        && (countDImplies(res) < countDImplies(f))
        && forall((i : BigInt) => i == i)
    )

    def applyRule2(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Implies])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Implies(f1, f2) = f
        val result = Or(Not(f1), f2)
        
        assert(weightOfAnds(result) <= weightOfAnds(f))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) <= weightOfAnds(f))
        && (countDImplies(res) <= countDImplies(f))
        && (countImplies(res) < countImplies(f))
    )

    def applyRule3(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Or])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Or(f1, f2) = f
        require(f2.isInstanceOf[And])
        val And(f21, f22) = f2
        val result = And(Or(f1, f21), Or(f1, f22))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) < weightOfAnds(f))
    )

    def applyRule4(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Or])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Or(f1, f2) = f
        require(f1.isInstanceOf[And])
        val And(f11, f12) = f1
        val result = And(Or(f11, f2), Or(f12, f2))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) < weightOfAnds(f))
    )

    def applyRule5(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Or])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Or(f1, f2) = f
        require(f2.isInstanceOf[Or])
        val Or(f21, f22) = f2
        val result = Or(Or(f1, f21), f22)
        
        Rule5Prop(f1, f21, f22, orsAboveLeft)
        assert (countOrPairs(result, orsAboveLeft) < countOrPairs(f, orsAboveLeft))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) <= weightOfAnds(f))
        && (countDImplies(res) <= countDImplies(f))
        && (countImplies(res) <= countImplies(f))
        && (countOrPairs(res, orsAboveLeft) < countOrPairs(f, orsAboveLeft))
    )

    def applyRule6(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[And])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val And(f1, f2) = f
        require(f2.isInstanceOf[And])
        val And(f21, f22) = f2
        val result = And(And(f1, f21), f22)
        
        Rule6Prop(f1, f21, f22, andsAboveLeft)
        assert (countAndPairs(result, andsAboveLeft) < countAndPairs(f, andsAboveLeft))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) <= weightOfAnds(f))
        && (countDImplies(res) <= countDImplies(f))
        && (countImplies(res) <= countImplies(f))
        && (countOrPairs(res, orsAboveLeft) <= countOrPairs(f, orsAboveLeft))
         && (countAndPairs(res, andsAboveLeft) < countAndPairs(f, andsAboveLeft))
    )

    def applyRule7(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Not])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Not(f1) = f
        require(f1.isInstanceOf[Or])
        val Or(f11, f12) = f1
        val result = And(Not(f11), Not(f12))
        
        Rule7Prop(f11, f12)
        assert (weightOfAnds(result) < weightOfAnds(f))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) < weightOfAnds(f))
    )

    def applyRule8(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Not])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Not(f1) = f
        require(f1.isInstanceOf[And])
        val And(f11, f12) = f1
        val result = Or(Not(f11), Not(f12))
        
        Rule8Prop(f11, f12)
        assert (weightOfAnds(result) < weightOfAnds(f))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) < weightOfAnds(f))
    )

    def applyRule9(f : FormulaT, orsAboveLeft : BigInt, andsAboveLeft : BigInt) : FormulaT = {

        require(formula.validFormulaT(f))
        require(f.isInstanceOf[Not])
        require(orsAboveLeft >= 0)
        require(andsAboveLeft >= 0)
        
        val Not(f1) = f
        require(f1.isInstanceOf[Not])
        val Not(f11) = f1
        val result = f1
        
        Rule9Prop(f11)
        assert (weightOfAnds(result) < weightOfAnds(f))

        result
    } ensuring(res =>
        (validFormulaT(res))
        && (weightOfAnds(res) < weightOfAnds(f))
    )


    /////////////////////
    ///// FUNCTIONS /////
    /////////////////////

    // @induct // we receive termination errors when trying to induct over this method
    def weightOfAnds(f : FormulaT) : BigInt = {
        decreases(f)
        f match {
            case Var(v)           => BigInt(2)
            case Not(f1)          => pow(2, weightOfAnds(f1))
            case Or(f1, f2)       => weightOfAnds(f1) * weightOfAnds(f2)
            case And(f1, f2)      => weightOfAnds(f1) + weightOfAnds(f2) + BigInt(1)
            case Implies(f1, f2)  => pow(BigInt(2), weightOfAnds(f1)) * weightOfAnds(f2)
            case DImplies(f1, f2) => pow(BigInt(2), weightOfAnds(f1)) * weightOfAnds(f2) +
                pow(BigInt(2), weightOfAnds(f2)) * weightOfAnds(f1) + BigInt(1)
        }
    } ensuring(
        res => res >= 2
    )

    // @induct // we don't receive errors on induction but the verification doesn't seem to need this
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

    def countImplies(f: FormulaT) : BigInt = {

        f match {
            case Var(v)           => BigInt(0)
            case Not(f1)          => countImplies(f1)
            case Or(f1, f2)       => countImplies(f1) + countImplies(f2)
            case And(f1, f2)      => countImplies(f1) + countImplies(f2)
            case Implies(f1, f2)  => countImplies(f1) + countImplies(f2) + 1
            case DImplies(f1, f2) => countImplies(f1) + countImplies(f2)
        }
    } ensuring(
        res => res >= 0
    )

    // @induct
    def countOrPairs(f: FormulaT, orsAboveLeft : BigInt) : BigInt = {
        require(orsAboveLeft >= 0)

        f match {
            case Var(v)           => BigInt(0)
            case Not(f1)          => countOrPairs(f1, orsAboveLeft)
            case Or(f1, f2)       => countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft + 1) + orsAboveLeft
            case And(f1, f2)      => countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft)
            case Implies(f1, f2)  => countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft)
            case DImplies(f1, f2) => countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft)
        }
    } ensuring(
        res => res >= 0
    )

    def countAndPairs(f: FormulaT, andsAboveLeft : BigInt) : BigInt = {
        require(andsAboveLeft >= 0)

        f match {
            case Var(v)           => BigInt(0)
            case Not(f1)          => countAndPairs(f1, andsAboveLeft)
            case Or(f1, f2)       => countAndPairs(f1, andsAboveLeft) + countAndPairs(f2, andsAboveLeft)
            case And(f1, f2)      => countAndPairs(f1, andsAboveLeft) + countAndPairs(f2, andsAboveLeft + 1) + andsAboveLeft
            case Implies(f1, f2)  => countAndPairs(f1, andsAboveLeft) + countAndPairs(f2, andsAboveLeft)
            case DImplies(f1, f2) => countAndPairs(f1, andsAboveLeft) + countAndPairs(f2, andsAboveLeft)
        }
    } ensuring(
        res => res >= 0
    )

    /////////////////////
    ///// LEMMAS ////////
    /////////////////////

    // @induct
    def mult2_upper(x : BigInt) : Boolean = {

        require(x >= 0)
        2 * x < 1+ pow(2, x)
    }.holds

    // def Rule5Prop(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT, orsAboveLeft : BigInt) : Boolean = {

    //     require(orsAboveLeft >= 0)

    //     countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft) ==
    //         countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft + 1) +
    //         countOrPairs(f3, orsAboveLeft + 2) + orsAboveLeft + orsAboveLeft + 1
    //     countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) ==
    //         countOrPairs(f1, orsAboveLeft) +
    //         countOrPairs(f2, orsAboveLeft + 1) +
    //         countOrPairs(f3, orsAboveLeft + 1) + orsAboveLeft + orsAboveLeft
    //     Rule5PropAux(f3, orsAboveLeft + 1)
    //     // countOrPairs(f3, orsAboveLeft +1) <= countOrPairs(f3, orsAboveLeft + 2)
    //     countOrPairs(f3, orsAboveLeft + 1) <= countOrPairs(f3, orsAboveLeft + 2)
    //     countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) <
    //         countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft)
    // }.holds

    // def Rule5PropAux(f : FormulaT, orsAboveLeft : BigInt) : Unit = {
    //     require(orsAboveLeft >= 0)

  
    //     assert(countOrPairs(f, orsAboveLeft) <= countOrPairs(f, orsAboveLeft + 1))
    // }

    def Rule5PropAux2(f : FormulaT, orsAboveLeft : BigInt) : Boolean = {
        require (orsAboveLeft >= 0)

        (countOrPairs(f, orsAboveLeft) <= countOrPairs(f, orsAboveLeft + 1)) because {
            f match {
                case Var(v)           => true
                case Not(f1)          => Rule5PropAux2(f1, orsAboveLeft)
                case Or(f1, f2)       => Rule5PropAux2(f1, orsAboveLeft) && Rule5PropAux2(f2, orsAboveLeft + 1)
                case And(f1, f2)      => Rule5PropAux2(f1, orsAboveLeft) && Rule5PropAux2(f2, orsAboveLeft)
                case Implies(f1, f2)  => Rule5PropAux2(f1, orsAboveLeft) && Rule5PropAux2(f2, orsAboveLeft)
                case DImplies(f1, f2) => Rule5PropAux2(f1, orsAboveLeft) && Rule5PropAux2(f2, orsAboveLeft)
            }
        }   
    }.holds

    def foo(x: BigInt): Unit = {
        check(x >= 0 || x < 0)
        check(x + 0 == x)
    }

    
    def Rule5Prop(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT, orsAboveLeft : BigInt) : Unit = {

        require(orsAboveLeft >= 0)

        check(countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft) ==
            countOrPairs(f1, orsAboveLeft) + 
            countOrPairs(f2, orsAboveLeft + 1) +
            countOrPairs(f3, orsAboveLeft + 2) + orsAboveLeft + orsAboveLeft + 1)
        check(countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) ==
            countOrPairs(f1, orsAboveLeft) +
            countOrPairs(f2, orsAboveLeft + 1) +
            countOrPairs(f3, orsAboveLeft + 1) + orsAboveLeft + orsAboveLeft)
        Rule5PropAux2(f3, orsAboveLeft + 1)
        check(countOrPairs(f3, orsAboveLeft +1) <= countOrPairs(f3, orsAboveLeft + 2))
        // countOrPairs(f3, orsAboveLeft + 1) <= countOrPairs(f3, orsAboveLeft + 2)
        check(countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) <
            countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft))
    }

    def Rule6PropAux(f : FormulaT, andsAboveLeft : BigInt) : Boolean = {
        require (andsAboveLeft >= 0)

        (countAndPairs(f, andsAboveLeft) <= countAndPairs(f, andsAboveLeft + 1)) because {
            f match {
                case Var(v)           => true
                case Not(f1)          => Rule6PropAux(f1, andsAboveLeft)
                case Or(f1, f2)       => Rule6PropAux(f1, andsAboveLeft) && Rule6PropAux(f2, andsAboveLeft)
                case And(f1, f2)      => Rule6PropAux(f1, andsAboveLeft) && Rule6PropAux(f2, andsAboveLeft + 1)
                case Implies(f1, f2)  => Rule6PropAux(f1, andsAboveLeft) && Rule6PropAux(f2, andsAboveLeft)
                case DImplies(f1, f2) => Rule6PropAux(f1, andsAboveLeft) && Rule6PropAux(f2, andsAboveLeft)
            }
        }   
    }.holds

    def Rule6Prop(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT, andsAboveLeft : BigInt) : Unit = {

        require(andsAboveLeft >= 0)

        check (countAndPairs(And(f1, And(f2, f3)), andsAboveLeft) ==
            countAndPairs(f1, andsAboveLeft) +
            countAndPairs(f2, andsAboveLeft + 1) +
            countAndPairs(f3, andsAboveLeft + 2) + andsAboveLeft + andsAboveLeft + 1)
        check (countAndPairs(And(And(f1, f2), f3), andsAboveLeft) ==
            countAndPairs(f1, andsAboveLeft) +
            countAndPairs(f2, andsAboveLeft + 1) +
            countAndPairs(f3, andsAboveLeft + 1) + andsAboveLeft + andsAboveLeft)
        Rule6PropAux(f3, andsAboveLeft + 1)
        check (countAndPairs(f3, andsAboveLeft + 1) <=
            countAndPairs(f3, andsAboveLeft + 2))
        check (countAndPairs(And(And(f1, f2), f3), andsAboveLeft) <
            countAndPairs(And(f1, And(f2, f3)), andsAboveLeft))
    }

    def Rule7Prop(f1 : FormulaT, f2 : FormulaT) : Unit = {

        require (weightOfAnds(f1) >= 2)
        require (weightOfAnds(f2) >= 2)

        assert( weightOfAnds(And(Not(f1), Not(f2))) ==
            pow(2, weightOfAnds(f1)) + pow(2, weightOfAnds(f2)) + 1)

        assert (weightOfAnds(Not(Or(f1, f2))) ==
            pow(2, weightOfAnds(f1) * weightOfAnds(f2)))
        if (weightOfAnds(f1) >= weightOfAnds(f2)) {
            sumpow_upper(weightOfAnds(f1), weightOfAnds(f2))
            assert (pow(2, weightOfAnds(f1)) + pow(2, weightOfAnds(f2)) + 1 <
                pow(2, weightOfAnds(f1) * weightOfAnds(f2)))
            assert (weightOfAnds(And(Not(f1), Not(f2))) <
                weightOfAnds(Not(Or(f1, f2))))
        } else {
            sumpow_upper(weightOfAnds(f2), weightOfAnds(f1))
        }
    }

    def Rule8Prop(f1 : FormulaT, f2 : FormulaT) : Unit = {

        require (weightOfAnds(f1) >= 2)
        require (weightOfAnds(f2) >= 2)

        assert (weightOfAnds(Or(Not(f1), Not(f2))) ==
            pow(2, weightOfAnds(f1)) * pow(2, weightOfAnds(f2)))

        assert (weightOfAnds(Not(And(f1, f2))) ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2) + 1))

        assert (pow(2, weightOfAnds(f1) + weightOfAnds(f2)) * 2 ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2) + 1))

        multpow_powsum(weightOfAnds(f1), weightOfAnds(f2))

        assert (pow(2, weightOfAnds(f1)) * pow(2, weightOfAnds(f2)) ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2)))
    }

    def Rule9Prop(f1 : FormulaT) : Unit = {

        require (weightOfAnds(f1) >= 2)

        pow_increases(weightOfAnds(f1));
        pow_increases(pow(2, weightOfAnds(f1)));

        assert (weightOfAnds(Not(Not(f1))) == pow(2, pow(2, weightOfAnds(f1))))
    }

    def Rule3Or(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT, andsAboveLeft : BigInt) : Unit = {

        require (weightOfAnds(f3) < weightOfAnds(f2))
        require (weightOfAnds(f1) >= 2)
        require (weightOfAnds(f2) >= 2)
        require (weightOfAnds(f3) >= 2)

        assert (weightOfAnds(Or(f1, f3)) == weightOfAnds(f1) * weightOfAnds(f3))
        assert (weightOfAnds(Or(f1, f2)) == weightOfAnds(f1) * weightOfAnds(f2))
        lessthan_mult_right(weightOfAnds(f1), weightOfAnds(f2), weightOfAnds(f3))
        assert (weightOfAnds(f1) * weightOfAnds(f3) < weightOfAnds(f1) * weightOfAnds(f2))
    }

}