package distribution


import FifoNetwork._
import Networking._

import leon.lang._
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
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
    
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
  
  @extern
  def printing(s: String) = {
    println(s)
  }
  
  @ignore
  def main(args: Array[String]) = {
    val a1 = CountingActor(actor1)
    val a2 = CheckingActor(actor2)
    
    runActors(NoParam(), a1, List(
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor1, Increment()),
      (actor1, actor2, Deliver(1)),
      (actor1, actor2, Deliver(2)),
      (actor1, actor2, Deliver(3)),
      (actor1, actor2, Deliver(4)),
      (actor1, actor2, Deliver(5))
    ))
  }

  
}


