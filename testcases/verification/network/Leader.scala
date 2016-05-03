package distribution


import FifoNetwork._
import Networking._
import IntQuantifiers._

import leon.lang._
import leon.collection._
import leon.proof._
import leon.annotation._
import leon.lang.synthesis._

import scala.language.postfixOps

// following https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm

object Protocol {
  import ProtocolProof._
  
  case class Election(i: BigInt) extends Message
  case class Elected(i: BigInt) extends Message

  case class NonParticipant() extends State
  case class Participant() extends State
  case class KnowLeader(i: BigInt) extends State
  
  case class UID(uid: BigInt) extends ActorId
  
  case class Params(n: BigInt, starterProcess: BigInt) extends Parameter
  
  
  def increment(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i < n-1) i+1
    else BigInt(0)
  } ensuring(res => 0 <= res && res < n)
    
  case class Process(myId: ActorId) extends Actor {
    val UID(myuid) = myId
  
    def init()(implicit net: VerifiedNetwork) = {
      require(initPre(this))
      val Params(n, starterProcess) = net.param
    
      if (myuid == starterProcess) {
        val nextProcess = UID(increment(myuid, n))
        update(Participant())
        !! (nextProcess, Election(myuid))
      }
    }
    
    
    def receive(sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
      require(receivePre(this, sender, m))
      
      val Params(n, starterProcess) = net.param
      val nextProcess = UID(increment(myuid, n))
    
      (sender, m, state) match {
        case (id, Election(uid), NonParticipant()) =>
          if (uid > myuid) {
            update (Participant())
            !! (nextProcess, Election(uid))
          } else if (uid < myuid) {
            update (Participant())
            !! (nextProcess, Election(myuid))
          }
          else {
            // I cannot receive an Election message equal to my uid if I'm not a participant
//             assert(false)
            ()
          }
          
        case (id, Election(uid), Participant()) =>
          if (uid > myuid) {
            !! (nextProcess, Election(uid))
          } else if (uid == myuid) {
            update (KnowLeader(uid))
            !! (nextProcess, Elected(myuid))
            // I'm the leader!!
          } else {
            // discard smaller uid Election message
          }
          
        case (id, Elected(_), NonParticipant()) =>
          // I cannot receive an Elected message if I didn't even participate yet
//           assert(false)
            ()
          
        case (id, Elected(uid), Participant()) => {
          update (KnowLeader(uid))
          !! (nextProcess, Elected(uid))
        }
        
        case (id, Elected(uid), KnowLeader(uid2)) => {
          ()
//           assert(uid == uid2)
        }
        
        case _ => {
//           assert(false)
          ()
        }
              
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  }
  
}


// This object contains lemma and auxialiary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  
  def init_states_fun(id: ActorId): Option[State] = Some(NonParticipant())
  def init_getActor_fun(id: ActorId): Option[Actor] = Some(Process(id))
  
  val init_states: MMap[ActorId,State] = MMap(init_states_fun)
  val init_getActor = MMap(init_getActor_fun)
  val init_messages = MMap[(ActorId,ActorId), List[Message]]()
  

  def makeNetwork(p: Parameter) = {
    require {
      val Params(n, starterProcess) = p
      validParam(p) && 
      init_statesDefined(n) && 
      init_getActorDefined(n) && 
      init_ringChannels(n) && 
      intForAll(n, statesDefined(init_states)) &&
      intForAll(n, getActorDefined(init_getActor)) &&
      intForAll2(n, ringChannels(n, MMap()))
    }
    
    val Params(n, starterProcess) = p
    
    val messages: MMap[(ActorId,ActorId), List[Message]] = MMap()
    
    
    VerifiedNetwork(p, init_states, messages, init_getActor)
  }
  
  
  def validParam(p: Parameter) = {
    val Params(n, starter) = p
    0 <= starter && starter < n
  }
  
  def validGetActor(net: VerifiedNetwork, id: ActorId) = {
    require(validId(net,id))
    
    val UID(uid) = id
    val Params(n,_) = net.param
    
    elimForAll(n, getActorDefined(net.getActor), uid) && 
    net.getActor.contains(id)
  } holds
  
  def existsMessage(n: BigInt,  messages: MMap[(ActorId,ActorId),List[Message]], m: Message) = {
    require(n >= 0)
    intExists(n, (i: BigInt) => 0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).contains(m))
  }
  
  def statesDefined(states: MMap[ActorId,State]) = {
    (i: BigInt) => states.contains(UID(i))
  }
  
  def init_ringChannels(n: BigInt): Boolean =  {
    if (n <= 0) intForAll2(n, ringChannels(n, MMap()))
    else init_ringChannels(n-1) && intForAll2(n, ringChannels(n, MMap()))
  }
  
  def init_statesDefined(n: BigInt): Boolean = {
    
    if (n <= 0) intForAll(n, statesDefined(init_states))
    else init_statesDefined(n-1) && init_states.contains(UID(n-1)) && intForAll(n, statesDefined(init_states))
    
  } holds
  
  
  def init_getActorDefined(n: BigInt): Boolean = {
    
    if (n <= 0) intForAll(n, getActorDefined(init_getActor))
    else init_getActorDefined(n-1) && intForAll(n, getActorDefined(init_getActor))
    
  } holds
  
  def getActorDefined(getActor: MMap[ActorId,Actor])(i: BigInt) = {
    getActor.contains(UID(i)) && getActor(UID(i)) == Process(UID(i))
  }
  
  
  def statesStillDefined(n: BigInt, states: MMap[ActorId,State], id: ActorId, s: State): Boolean = {
    require(intForAll(n, statesDefined(states)))
    
    if (n <= 0) 
      intForAll(n, statesDefined(states.updated(id,s)))
    else 
      states.updated(id,s).contains(UID(n-1)) && 
      statesStillDefined(n-1, states, id,  s) && 
      intForAll(n, statesDefined(states.updated(id,s)))
  
  } holds
  
  def smallChannel(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]])(i: BigInt) = {
    0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).size < 2
  }
  
  def ringChannels(n: BigInt, messages: MMap[(ActorId,ActorId),List[Message]])(i: BigInt, j: BigInt) = {
    0 <= i && i < n && (messages.contains(UID(i),UID(j)) ==> (j == increment(i,n)))
  }
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    val Params(n, starterProcess) = param
    validParam(param) && 
    intForAll(n, statesDefined(states)) &&
    intForAll(n, getActorDefined(getActor))  &&
    intForAll2(n, ringChannels(n, messages))
//     intForAll2(n, (i: BigInt, j: BigInt) => 
//     ) 
//     intForAll(n, smallChannel(n, messages))
      
//     intForAll2(n, (i: BigInt, j: BigInt) => 
//       0 <= i && i < n && elimForAll(n, (k: BigInt) => states.contains(UID(k)), i) &&
//       0 <= j && j < n && elimForAll(n, (k: BigInt) => states.contains(UID(k)), j) &&
//       ((states(UID(i)), states(UID(j))) match {
//         case (KnowLeader(a), KnowLeader(b)) => a == b
//         case _ => true
//       })
//     ) && 
//     intForAll2(n, (i: BigInt, j: BigInt) => 
//       0 <= i && i < n &&
//       0 <= j && j < n &&
//       (
//         messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).isEmpty || 
//         messages.getOrElse((UID(i), UID(increment(j,n))), Nil()).isEmpty
//       )
//     ) &&
//     intForAll2(n, (i: BigInt, j: BigInt) =>
//       states.contains(UID(i)) &&
//       states.contains(UID(j)) &&
//       (existsMessage(n, messages, Election(i)) ==> (
//         states(UID(i)) == Participant() &&
//         (states(UID(j)) match {
//           case KnowLeader(_) => false
//           case _ => true
//         })
//       ))
//     ) &&
//     intForAll2(n, (i: BigInt, j: BigInt) =>
//       states.contains(UID(i)) &&
//       states.contains(UID(j)) &&
//       (existsMessage(n, messages, Elected(i)) ==>  (
//         states(UID(i)) == KnowLeader(i) &&
//         (states(UID(j)) match {
//           case KnowLeader(i2) => i == i2
//           case NonParticipant() => false
//           case Participant() => true
//         })
//       ))
//     )
  }
  
  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
//     true
    val sms = net.messages.getOrElse((sender, receiver), Nil())
    
    val Params(n, starterProcess) = net.param
        
    val UID(usender) = sender
    val UID(ureceiver) = receiver 
    
    0 <= usender && usender < n && 
    0 <= ureceiver && ureceiver < n && 
    (sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = net.messages.updated((sender, receiver), xs)
        elimForAll(n, getActorDefined(net.getActor), ureceiver) &&
        net.getActor.contains(receiver) && 
        net.getActor(receiver) == Process(receiver) &&
        networkInvariant(net.param, net.states, messages2, net.getActor)
      case _ => 
        true
    })
  }
  
  def mapUpdate[A,B](m: MMap[A,B], k: A, v: B, k2: A) = {
    val newMap = m.updated(k, v)
    newMap.contains(k2) ==> (m.contains(k2) || k2 == k)
  } holds
  

  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    val UID(myuid) = a.myId
    val Params(n, starterProcess) = net.param
    val states = net.states
    
    if (myuid == starterProcess) {
      val nextProcess = UID(increment(myuid, n))
      val newStates = net.states.updated(a.myId, Participant())
      val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
      val newChannel = channel :+ Election(myuid)
      val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
      
      0 <= myuid && myuid < n &&
      intForAll(n, statesDefined(states))  &&
      statesStillDefined(n, states, a.myId, Participant()) &&
      intForAll(n, statesDefined(states.updated(a.myId, Participant()))) &&
      networkInvariant(net.param, newStates, net.messages, net.getActor) &&
      networkInvariant(net.param, newStates, newMessages, net.getActor)
  //       update(Participant())
  //       !! (nextProcess, Election(myuid))
    }
    else {
      true
    }
  }
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    
    val UID(myuid) = a.myId
    val Params(n, starterProcess) = net.param
    val states = net.states
  
    0 <= myuid && myuid < n  &&
    {
      val nextProcess = UID(increment(myuid, n))
      intForAll(n, statesDefined(states)) &&
      elimForAll(n, statesDefined(states), myuid) &&
        ((sender, m, a.state) match {
          case (id, Election(uid), NonParticipant()) =>
            if (uid > myuid) {
//               update (Participant())
//               !! (nextProcess, Election(uid))
              val newStates = states.updated(a.myId, Participant())
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
//               true

              intForAll(n, statesDefined(states)) &&
              statesStillDefined(n, states, a.myId, Participant())  &&
              intForAll(n, statesDefined(states.updated(a.myId, Participant()))) &&
              networkInvariant(net.param, newStates, net.messages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
            } 
            else if (uid < myuid) {
//             update (Participant())
//             !! (nextProcess, Election(myuid))
              val newStates = net.states.updated(a.myId, Participant())
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(myuid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)

              intForAll(n, statesDefined(states))  &&
              statesStillDefined(n, states, a.myId, Participant()) &&
              intForAll(n, statesDefined(newStates)) &&
              networkInvariant(net.param, newStates, net.messages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
            }
            else {
              // I cannot receive an Election message equal to my uid if I'm not a participant
                true
//               false
            }
            
          case (id, Election(uid), Participant()) =>
            if (uid > myuid) {
//               !! (nextProcess, Election(uid))
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
              
              true
//               networkInvariant(net.param, net.states, newMessages, net.getActor)
            } else if (uid == myuid) {
//               update (KnowLeader(uid))
//               !! (nextProcess, Elected(myuid))
              val newStates = net.states.updated(a.myId, KnowLeader(uid))
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Elected(myuid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)

              intForAll(n, statesDefined(states))  &&
              statesStillDefined(n, states, a.myId, KnowLeader(uid)) &&
              intForAll(n, statesDefined(newStates)) &&
              networkInvariant(net.param, newStates, net.messages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
            } else {
              true
              // discard smaller uid Election message
            }
            
          case (id, Elected(_), NonParticipant()) =>
            // I cannot receive an Elected message if I didn't even participate yet
            true
//             false
            
          case (id, Elected(uid), Participant()) => {
//               update (KnowLeader(uid))
//               !! (nextProcess, Elected(uid))
              val newStates = net.states.updated(a.myId, KnowLeader(uid))
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Elected(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
              
              intForAll(n, statesDefined(states)) &&
              statesStillDefined(n, states, a.myId, KnowLeader(uid)) &&
              intForAll(n, statesDefined(newStates)) &&
              networkInvariant(net.param, newStates, net.messages, net.getActor) 
//               &&
//               networkInvariant(net.param, newStates, newMessages, net.getActor)
          }
          
          case (id, Elected(uid), KnowLeader(uid2)) => {
//             uid == uid2
              true
          }
          
          case (id, Election(_), KnowLeader(_)) =>
            // there cannot be an election going on if I already know the Leader
              true
//             false
          
          case _ => {
              true
//             false
          }
        })
    }
  }
  
  def validId(net: VerifiedNetwork, id: ActorId) = {
    val UID(uid) = id
    val Params(n, _) = net.param
    0 <= uid && uid < n
  }
  
  
  @ignore
  def main(args: Array[String]) = {
//     val net = VerifiedNetwork(
//       
//     )
  }

}