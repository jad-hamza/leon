package distribution


import FifoNetwork._
import Networking._

import leon.lang.BooleanDecorations
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps


object Protocol {
  import ProtocolProof._
  
  case class Increment() extends Message
  case class Deliver(i: BigInt) extends Message

  case class CCounter(i: BigInt) extends State
  case class VCounter(i: BigInt) extends State
  case class BadState() extends State
  
  case class ActorId1() extends ActorId
  case class ActorId2() extends ActorId
  
  // this protocol does not need a parameter
  case class NoParam() extends Parameter
    
  val actor1: ActorId = ActorId1()
  val actor2: ActorId = ActorId2()
  
  case class CountingActor(myId: ActorId) extends Actor {
    require(myId == actor1)
  
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
    
      !! (actor1,Increment())
    }
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
    
      (sender, m, state) match {
        case (id,Increment(),CCounter(i)) if (id == myId) =>
          update (CCounter(i+1))
          !! (actor2, Deliver(i+1))
          !! (myId, Increment())
          
        case _ => update(BadState())
              
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  }
  
  
  
  case class CheckingActor(myId: ActorId) extends Actor {
    require(myId == actor2)
    
    def init()(implicit net: VerifiedNetwork) = ()
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
      check(sender == ActorId1())
      
      (sender, m, state) match {
      
        case (ActorId1(), Deliver(j), VCounter(k)) if (j > k) => update (VCounter(j))
        case _ => update(BadState())
      }
    }  ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
    
  }
  

  
}


// This object contains lemma and auxialiary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    states.contains(actor1) && 
    states.contains(actor2) &&
    states(actor1) != BadState() &&
    states(actor2) != BadState() &&
    getActor.contains(actor1) && 
    getActor.contains(actor2) && 
    getActor(actor1) == CountingActor(actor1) &&
    getActor(actor2) == CheckingActor(actor2) && 
    !messages.contains((actor2,actor2)) &&
    !messages.contains((actor2,actor1)) &&
    areIncrements(messages.getOrElse((actor1,actor1), Nil())) &&
    ((states(actor1),states(actor2)) match {
      case (CCounter(i),VCounter(k)) =>
        val sms = messages.getOrElse((actor1,actor2), Nil())
    
        areDelivers(sms) && 
        isSorted(sms) &&
        i >= k && (
          sms.isEmpty || (
            i >= max(sms) &&
            k < min(sms)
          )
        )
      case _ => false
      })
  }
  
    
    
  def countingActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    (sender, m, receiver.state) match {
      case (ActorId1(), Increment(), CCounter(i)) =>
    
        val j = i+1
        val a1a2messages = net.messages.getOrElse((actor1,actor2),Nil())
        val a1a1messages = net.messages.getOrElse((actor1,actor1),Nil())
        val newStates = net.states.updated(actor1, CCounter(j))
        val newa1a2messages = a1a2messages :+ Deliver(j)
        val newa1a1messages = a1a1messages :+ Increment()
        val newMapMessages = net.messages.updated((actor1,actor2), newa1a2messages)
        val newnewMapMessages = newMapMessages.updated((actor1,actor1), newa1a1messages)
        val VCounter(k) = net getState(actor2)
        
        areDelivers(a1a2messages) && 
        appendDeliver(a1a2messages, j) &&
        areIncrements(a1a1messages) && 
        appendIncrement(a1a1messages) && 
        areIncrements(newa1a1messages) && 
        areDelivers(newa1a2messages) &&
        appendDeliver(a1a2messages, j) &&
        appendItself(a1a2messages, j) &&
        j >= max(newa1a2messages) &&
        k < j &&
        appendLarger(a1a2messages, j, k) &&
        k < min(newa1a2messages) &&
        isSorted(a1a2messages) && 
        appendSorted(a1a2messages, j) && 
        isSorted(newa1a2messages) && 
        networkInvariant(net.param, newStates, newMapMessages, net.getActor) &&
        networkInvariant(net.param, newStates, newnewMapMessages, net.getActor)
        
      case _ => false
    }
    
  }
  
  def checkingActorReceivePre(receiver: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    sender == ActorId1() && 
    ((net getState(actor1), m, net getState(actor2)) match {
      case (CCounter(i), Deliver(j),VCounter(k)) =>
        val a1a2messages = net.messages.getOrElse((actor1,actor2),Nil())
        i >= j && j > k &&
          ( a1a2messages.isEmpty || j < min(a1a2messages) )
      case _ => false
    })
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    a match {
      case CountingActor(_) => countingActorReceivePre(a, sender, m)
      case CheckingActor(_) => checkingActorReceivePre(a, sender, m)
    }
  }
  
  def peekMessageEnsuresReceivePre(n: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    
    val sms = n.messages.getOrElse((sender, receiver), Nil())
    
  
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = n.messages.updated((sender, receiver), xs)
        
        (sender, receiver) match {
          case (ActorId1(), ActorId2()) => 
            
              ((n.getState(actor1), m, n.getState(actor2)) match {
                case (CCounter(i), Deliver(j),VCounter(k)) =>
                  val mm = messages2.getOrElse((actor1,actor2),Nil())

                  smallestHead(j,sms) && (mm.isEmpty || j < min(mm))
              })
            
          case (ActorId1(), ActorId1()) =>
            true
          
          case _ => 
              false
        }
      case _ => 
        true
    }
  }
  
  
  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    appendIncrement(net.messages.getOrElse((actor1,actor1), Nil()))
  }
  
  
  def min(l: List[Message]): BigInt = {
    require(!l.isEmpty && areDelivers(l))
    
    l match {
      case Cons(Deliver(i), Nil()) => i
      case Cons(Deliver(i), xs) =>
        val m = min(xs)
        if (i < m) i else m
    }
  }
  
  def max(l: List[Message]): BigInt = {
    require(!l.isEmpty && areDelivers(l))
    
    l match {
      case Cons(Deliver(i), Nil()) => i
      case Cons(Deliver(i), xs) =>
        val m = max(xs)
        if (i > m) i else m
    }
  }
  

  def isSorted(l: List[Message]): Boolean = {
    require(areDelivers(l))
    
    l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(Deliver(x), ls@Cons(Deliver(y), ys)) => x < y && isSorted(ls)
    }
  }
  
  def areDelivers(l: List[Message]): Boolean = {
    l match {
      case Nil() => true
      case Cons(Deliver(_), xs) => areDelivers(xs)
      case _ => false
    }
  }
  
  @induct 
  def appendDeliver(messages: List[Message], x: BigInt) = {
    require(areDelivers(messages))
    
    areDelivers(messages :+ Deliver(x))
  } holds
  
  def areIncrements(l: List[Message]): Boolean = {
    l match {
      case Nil() => true
      case Cons(Increment(), xs) => areIncrements(xs)
      case _ => false
    }
  }
  
  @induct 
  def appendIncrement(messages: List[Message]) = {
    require(areIncrements(messages))
    
    areIncrements(messages :+ Increment())
  } holds

  
  @induct
  def appendItself(l: List[Message], j: BigInt) = {
    require(areDelivers(l) && (l.isEmpty || j >= max(l)))
    
    appendDeliver(l,j) &&
    j >= max(l :+ Deliver(j))
  } holds
  
  @induct
  def appendLarger(l: List[Message], j: BigInt, k: BigInt) = {
    require(areDelivers(l) && (l.isEmpty || k < min(l)) && k < j)
    
    appendDeliver(l,j) &&
    k < min(l :+ Deliver(j))
  } holds
  
  @induct
  def appendSorted(l: List[Message], j: BigInt) = {
    require(l.isEmpty || (areDelivers(l) && isSorted(l) && j > max(l)))
  
    appendDeliver(l,j) &&
    isSorted(l :+ Deliver(j))
  } holds
  
  
  @induct
  def smallestHead(j: BigInt, l: List[Message]) = {
    require(areDelivers(l) && !l.isEmpty && isSorted(l))
    
    l match {
      case Cons(Deliver(j), xs) => xs.isEmpty || j < min(xs)
    }
  } holds
}