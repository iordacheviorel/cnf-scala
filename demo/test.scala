import stainless.lang._
import scala.language.postfixOps
import stainless.math.wrapping

object test {
  def ok = {
    assert(true)
  }
}

object TestMax {

  def rmax(x: BigInt, y: BigInt) = {
    if (x <= y) y else x
  }

  def max(x: BigInt, y: BigInt): BigInt = {
    val d = x - y
    if(d > 0) x else y
  } ensuring (res => res == rmax(x,y))
  def test1 = max(10, 5)
  def test2 = max(-5, 5)
  def test3 = max(-7, -5)

  def max_lemma(x: BigInt, y: BigInt, z:BigInt): Boolean = {

    max(x, x) == x &&
    max(x, y) == max(y, x) &&
    max(x,max(y,z)) == max(max(x,y), z) &&
    max(x,y) + z == max(x + z, y + z)
  } holds

  def old_max(x: Int, y: Int): Int = {
  require(0 >= x && 0 >= y)
  val d = wrapping(x - y)
  if (d > 0) x
  else y
} ensuring (res =>
  x <= res && y <= res && (res == x || res == y))

  def test4 = old_max(0, -2147483648)


}


