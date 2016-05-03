package distribution

import leon.lang._

import scala.language.postfixOps



object IntQuantifiers {

  def intForAll(n: BigInt, p: BigInt => Boolean): Boolean = {    
//     forall ((i: BigInt) => (0 <= i && i < n) ==> p(i))

    if (n <= 0) true
    else p(n-1) && intForAll(n-1,p)
  }

  def intExists(n: BigInt, p: BigInt => Boolean): Boolean = {    
//     ! forall ((i: BigInt) => (0 <= i && i < n) ==> !p(i))

    if (n <= 0) false
    else p(n-1) || intExists(n-1,p)
  }

  def intForAll2(n: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
//     forall ((i: BigInt, j: BigInt) => (0 <= i && i < n && 0 <= j && j < n) ==> p(i,j))

    if (n <= 0) true
    else 
      intForAll2(n-1, p) && 
      intForAll(n, (k: BigInt) => p(k,n-1)) &&
      intForAll(n, (k: BigInt) => p(n-1,k))
  }
  
  
  def elimForAll(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(intForAll(n, p) && 0 <= i && i < n)
    
//     decreaseLots(n, p, i+1)
    if (n <= 0) false
    else if (i == n-1) p(i)
    else intForAll(n-1, p) && elimForAll(n-1, p, i) && p(i)
    
  } holds
  
  def elimForAll2(n: BigInt, p: (BigInt, BigInt) => Boolean, i: BigInt, j: BigInt): Boolean = {
    require(intForAll2(n, p) && i >= 0 && i < n && 0 <= j && j < n)
    
    if (i == n-1) elimForAll(n, (k: BigInt) => p(n-1,k), j)
    else if (j == n-1) elimForAll(n, (k: BigInt) => p(k,n-1), i)
    else elimForAll2(n-1, p, i, j)

  } ensuring(_ => p(i,j))
  
  
  def elimExists(n: BigInt, p: BigInt => Boolean): BigInt = {
    require(intExists(n, p))
    
    if (p(n-1)) n-1
    else elimExists(n-1, p)
    
  } ensuring(res => p(res))
  
}