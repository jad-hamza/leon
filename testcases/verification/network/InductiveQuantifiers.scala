package distribution

import leon.lang._
import leon.proof._
import leon.annotation._

import scala.language.postfixOps



object Quantifiers {

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

  def intForAll2(n: BigInt, m: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
//     forall ((i: BigInt, j: BigInt) => (0 <= i && i < n && 0 <= j && j < n) ==> p(i,j))

    if (n <= 0 || m <= 0) true
    else p(n-1,m-1) && intForAll2(n-1, m, p) && intForAll2(n, m-1, p)
  }
  
  
  def elimForAll(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(intForAll(n, p) && 0 <= i && i < n)
    
//     decreaseLots(n, p, i+1)
    if (n <= 0) false
    else if (i == n-1) p(i)
    else intForAll(n-1, p) && elimForAll(n-1, p, i) && p(i)
    
  } holds
  
  def elimForAll2(n: BigInt, m: BigInt, p: (BigInt, BigInt) => Boolean, i: BigInt, j: BigInt): Boolean = {
    require(intForAll2(n, m, p) && 0 <= i && i < n && 0 <= j && j < m)
    
    if (i == n-1 && j == m-1) p(i,j)
    else if (i < n-1) elimForAll2(n-1, m, p, i, j) && p(i,j)
    else elimForAll2(n, m-1, p, i, j) && p(i,j)

  } holds
  
  
  def elimExists(n: BigInt, p: BigInt => Boolean): BigInt = {
    require(intExists(n, p))
    
    if (p(n-1)) n-1
    else elimExists(n-1, p)
    
  } ensuring(res => p(res))
  
  
  
  def notExistsImpliesForAll(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(!intExists(n,p))
    
    if (n <= 0)
      intForAll(n,(i: BigInt) => !p(i))
    else 
      notExistsImpliesForAll(n-1, p) && 
      intForAll(n,(i: BigInt) => !p(i))
  } holds
  
  
  def notForAllImpliesExists(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(!intForAll(n,p))
    
    if (n <= 0) false
    else if (!p(n-1))
      intExists(n, (i: BigInt) => !p(i))
    else 
      notForAllImpliesExists(n-1,p) &&
      intExists(n, (i: BigInt) => !p(i))
  } holds
  
  def witnessImpliesExists(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require (0 <= i && i < n && p(i))
  
    if (i == n-1) 
      intExists(n,p)
    else
      witnessImpliesExists(n-1, p, i) &&
      intExists(n, p)
  } holds






  def increment(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i < n-1) i+1
    else BigInt(0)
  } ensuring(res => 0 <= res && res < n)

  def decrement(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i == 0) n-1
    else i-1
  } ensuring(res => 0 <= res && res < n)



  def forAllModulo(n: BigInt, i: BigInt, j: BigInt, p: BigInt => Boolean): Boolean = {
    require (0 <= i && i < n && 0 <= j && j < n)

    if (i == j) p(j)
    else p(j) && forAllModulo(n, i, decrement(j,n), p)
  }

  def elimForAllModulo(n: BigInt, i: BigInt, j: BigInt, p: BigInt => Boolean, k: BigInt): Boolean = {
    require (
      0 <= i && i < n &&
      0 <= j && j < n &&
      0 <= k && k < n && (
        (i <= k && k <= j) ||
        (j < i && k >= i) ||
        (j < i && k <= j)
      ) &&
      forAllModulo(n, i, j, p)
    )

    if (i == j) p(k)
    else if (k == j) p(k)
    else elimForAllModulo(n, i, decrement(j,n), p, k) && p(k)
  } holds
}