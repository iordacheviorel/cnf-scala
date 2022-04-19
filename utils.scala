package cnf

import scala.language.postfixOps
import stainless.annotation._
import stainless.proof._ 
import stainless.proof.check

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
}