package distribution

import leon.lang._

import scala.language.postfixOps



object IntQuantifiers {

  def intForAll(n: BigInt, p: BigInt => Boolean): Boolean = {    
    forall ((i: BigInt) => (0 <= i && i < n) ==> p(i))

//     if (n <= 0) true
//     else p(n-1) && intForAll(n-1,p)
  }

  def intExists(n: BigInt, p: BigInt => Boolean): Boolean = {    
    ! forall ((i: BigInt) => (0 <= i && i < n) ==> !p(i))

//     if (n <= 0) false
//     else p(n-1) || intExists(n-1,p)
  }

  def intForAll2(n: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
    forall ((i: BigInt, j: BigInt) => (0 <= i && i < n && 0 <= j && j < n) ==> p(i,j))

//     if (n <= 0) true
//     else 
//       intForAll2(n-1, p) && 
//       intForAll(n, (k: BigInt) => p(k,n-1)) &&
//       intForAll(n, (k: BigInt) => p(n-1,k))
  }
  
  
  def decrease(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(intForAll(n, p))
    
    n <= 0 || intForAll(n-1, p)
  } holds
  
  

  def decreaseLots(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(n >= 0 && i >= 0 && i <= n && intForAll(n, p))

    if (i >= n-1) {
      intForAll(i, p)
    } else {
      decreaseLots(n-1, p, i)
      intForAll(i, p)
    }
  } holds
  
  
  def decrease2(n: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
    require(n >= 0 && intForAll2(n, p))
    
    n == 0 || intForAll2(n-1, p)
  } holds

  def decreaseLots2(n: BigInt, p: (BigInt, BigInt) => Boolean, i: BigInt): Boolean = {
    require(n >= 0 && i >= 0 && i <= n && intForAll2(n, p))

    if (i >= n-1) {
      intForAll2(i, p)
    } else {
      decreaseLots2(n-1, p, i)
      intForAll2(i, p)
    }
  } holds
  
  
  def elimForAll(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(intForAll(n, p) && i >= 0 && i < n)
    
//     decreaseLots(n, p, i+1) && // lemma application
    p(i)
  } holds
  
  
  def elimForAll2(n: BigInt, p: (BigInt, BigInt) => Boolean, i: BigInt, j: BigInt): Boolean = {
    require(intForAll2(n, p) && i >= 0 && i < n && 0 <= j && j < n)
    
//     if (i > j) {
//       decreaseLots2(n, p, i+1) && 
//       elimForAll(i+1, (k: BigInt) => p(i,k), j) &&
//       p(i,j)
//     } else {
//       decreaseLots2(n, p, j+1) && 
//       elimForAll(j+1, (k: BigInt) => p(k,j), i) &&
      p(i,j)
//     }
  } holds
  
  def elimExists(n: BigInt, p: BigInt => Boolean): BigInt = {
    require(intExists(n, p))
    
    if (p(n-1)) n-1
    else elimExists(n-1, p)
    
  } ensuring(res => p(res))
  
}