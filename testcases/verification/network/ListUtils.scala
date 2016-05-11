package distribution

import leon.collection._

object ListUtils {

  def contains[T](l: List[T], p: T => Boolean): Boolean = {
    l match {
      case Nil() => false
      case Cons(x, xs) => 
        if (p(x)) true
        else contains(xs, p)
    }
  }
}
