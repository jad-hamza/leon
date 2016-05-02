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
      val nextProcess = UID(increment(myuid, n))
    
      if (myuid == starterProcess) {
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
            assert(false)
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
          assert(false)
          
        case (id, Elected(uid), Participant()) => {
          update (KnowLeader(uid))
          !! (nextProcess, Elected(uid))
        }
        
        case (id, Elected(uid), KnowLeader(uid2)) => {
          assert(uid == uid2)
        }
        
        case _ => {
          assert(false)
        }
              
      }
    } ensuring(_ => networkInvariant(net.param, net.states, net.messages, net.getActor))
    
  }
  
}


// This object contains lemma and auxialiary functions used in the proofs

object ProtocolProof {
  import Protocol._
  
  
//   def restrictMessages(n: BigInt, l: List[Message], states: MMap[ActorId,State]): Boolean = {
//     require(intForAll(n, (i: BigInt) => states.contains(UID(i))))
//     
//     l match {
//       case Cons(Election(uid), ms) => 
//         0 <= uid && uid < n && elimForAll(n, (i: BigInt) => states.contains(UID(i)), uid) &&
//         (states(UID(uid))
//           match {
//             case Participant() => true
//             case _ => false
//           }
//         ) && ( 
//           intForAll(n, (i: BigInt) => 
//             0 <= i && i < n && elimForAll(n, (i: BigInt) => states.contains(UID(i)), i) &&
//             (states(UID(i)) match {
//               case KnowLeader(_) => 
//                 // you cannot know the leader if there is an election going on
//                 false
//               case _ => true
//             })
//           )
//         ) &&
//         restrictMessages(n, ms, states)
//       case Cons(Elected(uid), ms) => 
//         intForAll(n, (i: BigInt) => 
//           0 <= i && i < n && elimForAll(n, (i: BigInt) => states.contains(UID(i)), i) &&
//           (states(UID(i)) match {
//           case KnowLeader(uid2) => uid == uid2
//           case NonParticipant() => 
//             // the leader cannot be elected if I have not participated yet
//             false
//           case Participant() => true
//         })) && restrictMessages(n, ms, states)
//       case _ => true
//     }
//   }
  
  
  def existsMessage(n: BigInt,  messages: MMap[(ActorId,ActorId),List[Message]], m: Message) = {
    require(n >= 0)
    intExists(n, (i: BigInt) => 0 <= i && i < n && messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).contains(m))
  }
  
  // This is an invariant of the class VerifiedNetwork
  def networkInvariant(param: Parameter, states: MMap[ActorId, State], messages: MMap[(ActorId,ActorId),List[Message]], getActor: MMap[ActorId,Actor]) = {
    val Params(n, starterProcess) = param
    n > 1  && n == 2 &&
    0 <= starterProcess && starterProcess < n && 
    intForAll(n, (i: BigInt) => states.contains(UID(i))) &&
    intForAll(n, (i: BigInt) => getActor.contains(UID(i))) && 
    intForAll(n, (i: BigInt) =>
      0 <= i && i < n &&
      messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).size < 2
    ) && 
    intForAll(n, (i: BigInt) =>
      0 <= i && i < n && elimForAll(n, (k: BigInt) => getActor.contains(UID(k)), i) &&
      getActor(UID(i)).myId == UID(i)
    ) &&
    intForAll2(n, (i: BigInt, j: BigInt) => 
      0 <= i && i < n &&
      (messages.contains(UID(i),UID(j)) ==> (j == increment(i,n)))
    ) &&
    intForAll2(n, (i: BigInt, j: BigInt) => 
      0 <= i && i < n && elimForAll(n, (k: BigInt) => states.contains(UID(k)), i) &&
      0 <= j && j < n && elimForAll(n, (k: BigInt) => states.contains(UID(k)), j) &&
      ((states(UID(i)), states(UID(j))) match {
        case (KnowLeader(a), KnowLeader(b)) => a == b
        case _ => true
      })
    ) && 
    intForAll2(n, (i: BigInt, j: BigInt) => 
      0 <= i && i < n &&
      0 <= j && j < n &&
      (
        messages.getOrElse((UID(i), UID(increment(i,n))), Nil()).isEmpty || 
        messages.getOrElse((UID(i), UID(increment(j,n))), Nil()).isEmpty
      )
    ) &&
    intForAll2(n, (i: BigInt, j: BigInt) =>
      (existsMessage(n, messages, Election(i)) ==> (
        states(UID(i)) == Participant() &&
        (states(UID(j)) match {
          case KnowLeader(_) => false
          case _ => true
        })
      ))
    ) &&
    intForAll2(n, (i: BigInt, j: BigInt) =>
      (existsMessage(n, messages, Elected(i)) ==>  (
        states(UID(i)) == KnowLeader(i) &&
        (states(UID(j)) match {
          case KnowLeader(i2) => i == i2
          case NonParticipant() => false
          case Participant() => true
        })
      ))
    )
  }
  
  def peekMessageEnsuresReceivePre(net: VerifiedNetwork, sender: ActorId, receiver: ActorId, m: Message) = {
    
    val sms = net.messages.getOrElse((sender, receiver), Nil())
    
    val Params(n, starterProcess) = net.param
  
    sms match {
      case Cons(x, xs) if (x == m) => 
        val messages2 = net.messages.updated((sender, receiver), xs)
        
        val UID(usender) = sender
        val UID(ureceiver) = receiver 
        
        0 <= usender && usender < n && 
        ureceiver == increment(usender,n) && 
        elimForAll(n, (i: BigInt) => net.getActor.contains(UID(i)), ureceiver) &&
        net.getActor.contains(receiver)  &&
        networkInvariant(net.param, net.states, messages2, net.getActor)
//         &&
//         receivePre(net.getActor(receiver), sender, m)(net)
      case _ => 
        true
    }
  }
  
  def mapUpdate[A,B](m: MMap[A,B], k: A, v: B, k2: A) = {
    val newMap = m.updated(k, v)
    newMap.contains(k2) ==> (m.contains(k2) || k2 == k)
  } holds
  
  def receivePre(a: Actor, sender: ActorId, m: Message)(implicit net: VerifiedNetwork) = {
    
    val UID(myuid) = a.myId
    val Params(n, starterProcess) = net.param
  
    n > 1 && 
    0 <= myuid && myuid < n && {
      val nextProcess = UID(increment(myuid, n))
      (elimForAll(n, (i: BigInt) => net.states.contains(UID(i)), myuid))  && (
        (sender, m, a.state) match {
          case (id, Election(uid), NonParticipant()) =>
            if (uid > myuid) {
//               update (Participant())
//               !! (nextProcess, Election(uid))
              val newStates = net.states.updated(a.myId, Participant())
              val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
              val newChannel = channel :+ Election(uid)
              val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
              
//               true
              intForAll(n, (i: BigInt) => newStates.contains(UID(i))) &&
              intForAll2(n, (i: BigInt, j: BigInt) => 
                0 <= i && i < n && elimForAll(n, (k: BigInt) => net.states.contains(UID(k)), i) &&
                0 <= j && j < n && elimForAll(n, (k: BigInt) => net.states.contains(UID(k)), j) &&
                ((net.states(UID(i)), net.states(UID(j))) match {
                  case (KnowLeader(a), KnowLeader(b)) => a == b
                  case _ => true
                })
              )  

//               networkInvariant(net.param, newStates, net.messages, net.getActor)
            } 
            else if (uid < myuid) {
              true
            }
            else {
              // I cannot receive an Election message equal to my uid if I'm not a participant
              false
            }
            
          case (id, Election(uid), Participant()) =>
            if (uid > myuid) {
              true
            } else if (uid == myuid) {
              true
            } else {
              true
              // discard smaller uid Election message
            }
            
          case (id, Elected(_), NonParticipant()) =>
            // I cannot receive an Elected message if I didn't even participate yet
            false
            
          case (id, Elected(uid), Participant()) => {
//               update (KnowLeader(uid))
//               !! (nextProcess, Elected(uid))
            true
          }
          
          case (id, Elected(uid), KnowLeader(uid2)) => {
            uid == uid2
          }
          
          case (id, Election(_), KnowLeader(_)) =>
            // there cannot be an election going on if I already know the Leader
            false
          
          case _ => {
            false
          }
        })
    }
  }
  
  def initPre(a: Actor)(implicit net: VerifiedNetwork) = {
    val UID(myuid) = a.myId
    val Params(n, starterProcess) = net.param
    
    n > 1 && 0 <= myuid && myuid < n && {
      val nextProcess = UID(increment(myuid, n))
      if (myuid == starterProcess) {
        val newStates = net.states.updated(a.myId, Participant())
        val channel = net.messages.getOrElse((a.myId, nextProcess), Nil())
        val newChannel = channel :+ Election(myuid)
        val newMessages = net.messages.updated((a.myId, nextProcess), newChannel)
        networkInvariant(net.param, newStates, net.messages, net.getActor) &&
        networkInvariant(net.param, newStates, newMessages, net.getActor)
  //       update(Participant())
  //       !! (nextProcess, Election(myuid))
      }
      else {
        true
      }
    }
  }
  
  
  @ignore
  def main(args: Array[String]) = {
//     val net = VerifiedNetwork(
//       
//     )
  }

}