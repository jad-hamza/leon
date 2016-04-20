package distribution

import leon.collection._
import leon.lang._

case class MMap[A,B](f: A => Option[B]) {

  def contains(k: A): Boolean = f(k) != None[B]()

  
  def apply(k: A): B = {
    require(contains(k))
    
    f(k).get
     
  }
  
  def updated(k: A, v: B) = {
    MMap((x: A) => if (x == k) Some(v) else f(x))
  }
  
  def getOrElse(k: A, v: B) = {
    if (contains(k)) f(k).get
    else v
  }
}

object MMap {

  def apply[A,B](): MMap[A,B] = MMap((x: A) => None[B]())

}
