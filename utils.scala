package cnf

import scala.language.postfixOps
import stainless.annotation._
import stainless.proof._ 
import stainless.proof.check
import stainless.lang._ 

package object utils {

    // @induct
    def max(v1 : BigInt, v2 : BigInt) : BigInt = {
        require (v1 >= 0)
        require (v2 >= 0)

        if (v1 >= v2) 
            v1 
        else 
            v2
    } ensuring(res => 
        (res == v1 || res == v2) &&
        res >= v1 && res >= v2 && res >=0
        )

    
    
    def pow(exp : BigInt, power : BigInt) : BigInt = {

        require(power >= 0)
        require(exp > 0)
            
        if (power == 0)
            BigInt(1)
        else
            { 
                exp * pow(exp, power-1)
                // val np = power - BigInt(1)
                // assert(np < power)
                // val x = pow(exp, np)
                // assert(x > BigInt(0))
                // x * exp 
            }
    } ensuring(res => res > 0)

    /////////////////////
    //// LEMMAS /////////
    /////////////////////

    // @induct // by default in dafny
    def pow_monotone(a : BigInt, b : BigInt) : Boolean = {

        require(0 <= a)
        require(a <= b)

        (pow(2, a) <= pow(2, b)) because {
            if (a == b)  
                pow(2, a) == pow(2, b) 
            else
                pow_monotone(a, b - 1)
        }
    }.holds

    def pow_monotone_strict(a : BigInt, b : BigInt) : Boolean = {

        require(0 <= a)
        require(a < b)

        (pow(2, a) < pow(2, b)) because {
            if (a + 1 == b)  
                pow(2, a) < pow(2, b) 
            else
                pow_monotone_strict(a, b - 1)
        }
    }.holds

    def multpow_powsum(a : BigInt, b : BigInt) : Boolean = {

        require(a >= 1)
        require(b >= 1)

        (pow(2, a) * pow(2, b) == pow(2, a + b)) because {
            if (b > 2)  
                multpow_powsum(a, b - 1) 
            else
                pow(2, a) * pow(2, 2) == pow(2, a + 2)
        }
    }.holds


    def sumpow_upper(a : BigInt, b : BigInt) : Unit = {

        require(a >= 1)
        require(b >= 2)
        require(a >= b)

        pow_monotone(a * 2, a * b)
        assert (pow(2, a * 2) <= pow(2, a * b))
        assert (pow(2, a + a) <= pow(2, a * 2))
        multpow_powsum(a, a)
        assert (pow(2, a) * pow(2, a) <= pow(2, a + a))
        
        assert (4 <= pow(2, a))
        assert (4 * pow(2, a) <= pow(2, a) * pow(2, a))
        check (pow(2, a) + pow(2, a) + pow(2, a) + pow(2, a) <= 4 * pow(2, a))
        pow_monotone(b, a)
        check (pow(2, b) <= pow(2, a))
        check (pow(2, a) + pow(2, b) + 1 <
            pow(2, a) + pow(2, a) + pow(2, a) + pow(2, a))
    }

    def mult2_upper(x : BigInt) : Boolean = {

        require(x >= 0)

        (2 * x < 1 + pow(2, x)) because {
            if (x == 0)  
                true
            else
                mult2_upper(x - 1)
        }
    }

    // def lessthan_mult_right(a : BigInt, b : BigInt, c : BigInt) : Unit = {
    
    //     require(a >= 1)
    //     require(b >= 1)
    //     require(c >= 1)
    //     require(c < b)
        
    //     assert(a * c < a)

    // }




}