------------------------------ MODULE CrossChain ------------------------------
EXTENDS TLAPS, Integers, Sequences, TLC, FiniteSets
Integers   == Nat \ {0}

(* NTxs is the number of transactions, the number of traded assets and       *)
(* Correct the number of correct participants involved in the swap           *)
CONSTANT NTxs, Correct 

(*****************************************************************************)
(* AStates |-> asset's states                                                *)
(* CStates |-> coordinator's states, PStates |-> Publisher's states          *)
(* SwapStates |-> swap graph states                                          *)
(* AStates, AvailableR, CStates, PStates, SwapStates are DEFINITION for tlaps*)
(* PublisherID is the identifier of the publisher and CoordinatorID the      *)
(* identifier of the coordinator                                             *)
(*****************************************************************************)

AStates       == {"OwS", "OwR", "locked", "other"}
CStates       == {"init", "published", "okRM", "okRF"}
PStates       == {"init", "publish"}
SwapStates    == {"init", "correct", "different"}
PublisherID   == -1
CoordinatorID == 0

(*****************************************************************************)
(* Sources |-> the set of source's id                                        *)
(* Assets |-> the set of asset's id                                          *)
(* Recipients |-> the set of recipient's id                                  *)
(* Pi |-> the set of all sources and recipients                              *)
(* Pc |-> the set of correct sources and recipients                          *)
(* CSources |-> the set of correct sources                                   *)
(* CRecipients |-> the set of correct recipients                             *)
(* BSources |-> the set of byzantine sources                                 *)
(* BRecipients |-> the set of byzantine recipients                           *)
(*****************************************************************************)

Sources          == {3*x-2   : x \in 1..NTxs}
Assets           == {3*x-1   : x \in 1..NTxs}
Recipients       == {3*x     : x \in 1..NTxs}

Pi               == Sources \cup Recipients
Pc               == Pi \cap Correct

CSources         == Pc \cap Sources
CRecipients      == Pc \cap Recipients
BSources         == Sources \ CSources
BRecipients      == Recipients \ CRecipients

(*****************************************************************************)
(*AofS(x) is a function that gives the asset id of the source 'x'            *)
(*AofR(x) is a function that gives the asset id of the recipient 'x'         *)
(*SofA(x) is a function that gives the source id of the asset 'x'            *)
(*RofA(x) is a function that gives the recipient id of the asset 'x'         *)
(* AssetsFromCS |-> set of assets originally owned by a correct source       *)
(* AssetsForCR |-> set of assets intended for a correct recipient            *)
(*****************************************************************************)

AofS(x) == x + 1
AofR(x) == x - 1
SofA(x) == x - 1
RofA(x) == x + 1

AssetsFromCS     == {AofS(x) : x \in CSources}
AssetsForCR      == {AofR(x) : x \in CRecipients}

(*

--fair algorithm ACC {

(*****************************************************************************)
(* assets |-> list of all assets initialize to "OwS" state                   *)
(* pState |-> Publisher state initializes to "init"                          *)
(* coordState |-> coordinator state initializes to "init"                    *)
(* qrm |-> sequence of ask redeem call function                              *)
(* qrf |-> sequence of ask refund call function                              *)
(* swapGraph |-> swap graph state initializes to "init"                      *)
(* ProofPublish, ProofLock, ProofOkRM and ProofOkRF are proof-of-action      *)
(* describes in the article.                                                 *)
(*assets, pState, coordState, qrm, qrf, swapGraph and proof-of-action are    *)
(* VARIABLES for tlaps                                                       *)
(*****************************************************************************)

variable  
         assets          = [a \in Assets |-> "OwS"], 
         pState          = "init",
         coordState      = "init",  
         qrm = {},
         qrf = "false",
         swapGraph = "init",
         ProofPublish = "false",
         ProofLock =[c \in Sources |-> "false"],
         ProofOkRM = FALSE,
         ProofOkRF = FALSE;
         
(*****************************************************************************)
(*  the define block can be used in pluscal code                             *)
(* and in properties. The operator returns true if the expression is true    *)
(* ValidTransfer and AbortTransfer corresponds to the predicates of the same *)
(* name in the article                                                       *)
(* qrm = Sources -> all sources has been asked for a redeem authorization    *)
(*qrf = true -> at least one participant has asked for a refund authorization*)
(*****************************************************************************)

 define {
    ValidTransfer == qrm = Sources 
    AbortTransfer == qrf = "true" 
       }

(*****************************************************************************)
(* Macros are the general catch-all code inliner.                            *)
(* lockAsset(self) |-> locks the asset of the source self and set to true the*)
(* proof of action ProofLock[self]                                           *)
(*****************************************************************************)

macro lockAsset(self) {
   if (ProofPublish = "true" /\ self \in Sources /\ assets[AofS(self)] = "OwS")
   {assets[AofS(self)] := "locked";
    ProofLock[self] := "true";}
    }

    
(*****************************************************************************)
(* askRM(self) :                                                             *)
(*When a source asks for a redeem authorization, its lock proof has to be    *)
(* valid  and the coordinator has to be in the published state               *)
(*****************************************************************************)

macro askRM(self) 
 {if (self \in Sources /\ ProofLock[self] = "true" /\ coordState = "published") 
 {qrm := qrm \union {self};}
 }

(*****************************************************************************)
(* retrievingAsset(self) : the macro updates the assets' state to OwR        *)
(*****************************************************************************)

macro retrievingAsset(self) {
  if (self \in Recipients /\ ProofOkRM = TRUE /\ assets[AofR(self)] = "locked") 
  assets[AofR(self)] := "OwR"}
    
(*****************************************************************************)
(* askRF(self) : any participant can ask for a refund authorization          *)
(*****************************************************************************)

macro askRF(self) {
     if (coordState = "published")
     qrf := "true";
     }


(*****************************************************************************)
(* recoveringAsset(self) : the macro updates the assets' state to OwS        *)
(*****************************************************************************)


macro recoveringAsset(self) {
    if (self \in Sources /\ ProofOkRF = TRUE /\ assets[AofS(self)] ="locked") 
    assets[AofS(self)] := "OwS"}
    
(*****************************************************************************)
(* other(self) and directToR(self) are actions that byzantine can do         *)
(*other(self) describes the behavior of a byzantine where it can do anything *)
(* with its asset. directToR(self) it describes the direct send of its asset *)
(* to the recipient without waiting for the coordinator's decision           *)
(*****************************************************************************)
   
macro other(self) {
    if (self \in Sources /\ assets[AofS(self)] = "OwS") 
    assets[AofS(self)]:= "other";}
    
macro otherR(self) {
    if (self \in Recipients /\ assets[AofR(self)] = "OwR") 
    assets[AofR(self)]:= "other";}
    
macro directToR(self) {
if (self \in Sources /\ assets[AofS(self)] = "OwS") assets[AofS(self)]:= "OwR"}

macro directToS(self) {
if (self \in Recipients /\ assets[AofR(self)] = "OwR") assets[AofR(self)]:= "OwS"}

(*****************************************************************************)
(* We define the following processes: (1) the Publisher. (2) the coordinator *)
(*  (3) correct sources, (4) byzantine sources, (5) correct recipients and   *)
(* (6) byzantine recipients                                                  *)
(*                                                                           *)
(* The Publisher has -1 as an identifier (random identifier).                *)
(* it publish the swap graph, by changing its state to "publish". We assume  *)
(* that the publisher can be byzantine. Hence, the graph is either correct   *)
(*  or different from the graph constructed by the participants of the swap. *)
(* The publisher can halt, even if an action is enabled, stay in "init_p"    *)
(*forever and stutters. A process crash is modeled by having stuttering steps*)
(*****************************************************************************)

      process (Publisher = PublisherID)
    {
        init_p :  
               either {
                    pState := "publish"; 
                    either swapGraph := "correct";
                    or swapGraph := "different"; 
                      }  
               or skip;          
    };
  
(*****************************************************************************)
(* The coordinator has 0 as an identifier (random identifier).               *)
(* init_c : The coordinator waits for the Publisher to publish the graph     *)
(* to updates its state. When the state is updated, the proof of published   *)
(* is set to true.                                                           *)
(* decision : the decision is either redeem (if ValidTransfer is true) or    *)
(* the decision is refund (if AbortTransfer is true).                        *)
(* decisionValid: the coordinator updates to okRM state and the ProofOkRM is *)
(* available for recipients to retrieve their assets                         *)
(* decisionAbort: the coordinator updates to okRF state and the ProofOkRF is *)
(* available for sources to recover their assets.                            *)
(* the coordinator is a correct entity. We add to the process a fairness     *)
(* condition that the process cannot stop at a non-blocking action.          *)
(*****************************************************************************)

  fair   process (Coordinator = CoordinatorID)
   
    {
      
init_c:     
            await pState = "publish" /\ swapGraph # "init";
            coordState := "published";
            ProofPublish := "true";
decision:
            either {
                await ValidTransfer;
                decisionValid:
                coordState := "okRM";
                ProofOkRM := TRUE;
                goto Done;
                   }
            or {
                await AbortTransfer;
                decisionAbort:
                coordState := "okRF";
                ProofOkRF := TRUE;
                goto Done;
               };
    };

(*****************************************************************************)
(* Source is a multiprocess of CSources processes (correct sources).         *)
(* init_src : sources waits for the swap graph to be published               *)
(*  either the swap is different (in this case the source leaves the swap)   *)
(* or the graph is correct and the ProofPublish of the coordinator is valid  *)
(* if the graph is correct, correct sources can lock their asset (lock)      *)
(* and asks for a redeem decision (published).                               *)
(* waitForD: source waits for the coordinator decision                       *)
(* exit_src: when the decision is given, sources can exit the swap           *)
(*****************************************************************************)

 fair  process (Source \in CSources )

{
init_src : 
        \* the case where the swap is different or the timeout has been reached
          either { await swapGraph = "different" \/ TRUE;
                   goto Done;} 
          or     { await ProofPublish = "true" /\ swapGraph = "correct";
lock:              lockAsset(self);
          
published:         askRM(self );
   
waitForD:          either { await ProofOkRM = TRUE;
                            goto Done;}
                   or { await ProofOkRF = TRUE;
                        recoveringAsset(self);
                        goto Done;}
                   or {\* the case where NoDecision is true
                       await coordState = "published";
                       askRF(self);
                       goto waitForD;};
                    };
};

(*****************************************************************************)
(* BSource is a multiprocess of BSources processes (byzantine sources).      *)
(* Since a byzantine behavior cannot be predicted, we use the either         *)
(* statement to express the non determinisme of a byzantine.                 *)
(* a byzantine can execute the actions of a source in a completely random    *)
(* order in addition to the actions directToR and other.                     *)
(* As a result, it has the ability to run the protocol correctly and behaves *)
(* as a correct source. The process is unfair, thus we do not add the 'fair' *)
(* statement before process. We assume that the process can crash at anytime *)
(*****************************************************************************)


process (BSource \in BSources)
{
init_bsrc: 
  {
    either { BdirectToR: directToR(self); goto init_bsrc; } 
    or { Bother: other(self); goto init_bsrc; } 
    or {BaskRM: askRM(self ); goto init_bsrc; } 
    or { BlockAsset: lockAsset(self); goto init_bsrc; } 
    or { BSaskRF: askRF(self); goto init_bsrc; } 
    or { BrecoveringAsset: recoveringAsset(self); goto init_bsrc; };
  }
};

(*****************************************************************************)
(* Recipient is a multiprocess of CRecipients processes (correct recipients) *)
(* init_rcp: either the swap is correct or different                         *)
(* waitForD_rcp: the recipient waits for the coordinator decision.           *)
(*****************************************************************************)
    
 fair process (Recipient \in CRecipients) 
{
init_rcp : 
         either { await swapGraph = "different" \/ TRUE;
                  goto Done;}
         or { await ProofPublish = "true" /\ swapGraph = "correct";
waitForD_rcp:
              either { await ProofOkRF = TRUE;
                       goto Done;}
              or { await ProofOkRM = TRUE;
                   retrievingAsset(self);
                   goto Done;}
              or { await coordState = "published";
                   askRF(self);
                   goto waitForD_rcp;};
};
};

(*****************************************************************************)
(* BRecipient is a multiprocess of BRecipients processes(byzantine recipient)*)
(* As byzantine sources, a byzantine recipient behavior cannot be predicted  *)
(* a byzantine can execute the actions of a recipient in a completely random *)
(* order in addition to the actions.                                         *)
(* As a result, it has the ability to run the protocol correctly and behaves *)
(*as a correct recipient. The process is unfair,thus we do not add the 'fair'*)
(* statement before process. We assume that the process can crash at anytime *)
(*****************************************************************************)

process (BRecipient \in BRecipients)
{
init_brcp: 
either {BRaskRF: askRF(self); goto init_brcp;} 
or {BRretrievingAsset: retrievingAsset(self); goto init_brcp;}
or {BRdirectToS: directToS(self); goto init_brcp;}
or {BRother: otherR(self); goto init_brcp;};

};

};
  *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-c418a9ec943d5aeb0dde39e7d4ce1f52 (chksum(pcal) = "c7c16904" /\ chksum(tla) = "625c5903") (chksum(pcal) = "f588acdf" /\ chksum(tla) = "3581c091") (chksum(pcal) = "f588acdf" /\ chksum(tla) = "3581c091") (chksum(pcal) = "27c4cee6" /\ chksum(tla) = "4f961751") (chksum(pcal) = "c7c16904" /\ chksum(tla) = "625c5903") (chksum(pcal) = "34fb6831" /\ chksum(tla) = "d358fa00")
VARIABLES assets, pState, coordState, qrm, qrf, swapGraph, ProofPublish, 
          ProofLock, ProofOkRM, ProofOkRF, pc

(* define statement *)
ValidTransfer == qrm = Sources
AbortTransfer == qrf = "true"


vars == << assets, pState, coordState, qrm, qrf, swapGraph, ProofPublish, 
           ProofLock, ProofOkRM, ProofOkRF, pc >>

ProcSet == {PublisherID} \cup {CoordinatorID} \cup (CSources) \cup (BSources) \cup (CRecipients) \cup (BRecipients)

Init == (* Global variables *)
        /\ assets = [a \in Assets |-> "OwS"]
        /\ pState = "init"
        /\ coordState = "init"
        /\ qrm = {}
        /\ qrf = "false"
        /\ swapGraph = "init"
        /\ ProofPublish = "false"
        /\ ProofLock = [c \in Sources |-> "false"]
        /\ ProofOkRM = FALSE
        /\ ProofOkRF = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = PublisherID -> "init_p"
                                        [] self = CoordinatorID -> "init_c"
                                        [] self \in CSources -> "init_src"
                                        [] self \in BSources -> "init_bsrc"
                                        [] self \in CRecipients -> "init_rcp"
                                        [] self \in BRecipients -> "init_brcp"]

init_p == /\ pc[PublisherID] = "init_p"
          /\ \/ /\ pState' = "publish"
                /\ \/ /\ swapGraph' = "correct"
                   \/ /\ swapGraph' = "different"
             \/ /\ TRUE
                /\ UNCHANGED <<pState, swapGraph>>
          /\ pc' = [pc EXCEPT ![PublisherID] = "Done"]
          /\ UNCHANGED << assets, coordState, qrm, qrf, ProofPublish, 
                          ProofLock, ProofOkRM, ProofOkRF >>

Publisher == init_p

init_c == /\ pc[CoordinatorID] = "init_c"
          /\ pState = "publish" /\ swapGraph # "init"
          /\ coordState' = "published"
          /\ ProofPublish' = "true"
          /\ pc' = [pc EXCEPT ![CoordinatorID] = "decision"]
          /\ UNCHANGED << assets, pState, qrm, qrf, swapGraph, ProofLock, 
                          ProofOkRM, ProofOkRF >>

decision == /\ pc[CoordinatorID] = "decision"
            /\ \/ /\ ValidTransfer
                  /\ pc' = [pc EXCEPT ![CoordinatorID] = "decisionValid"]
               \/ /\ AbortTransfer
                  /\ pc' = [pc EXCEPT ![CoordinatorID] = "decisionAbort"]
            /\ UNCHANGED << assets, pState, coordState, qrm, qrf, swapGraph, 
                            ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

decisionValid == /\ pc[CoordinatorID] = "decisionValid"
                 /\ coordState' = "okRM"
                 /\ ProofOkRM' = TRUE
                 /\ pc' = [pc EXCEPT ![CoordinatorID] = "Done"]
                 /\ UNCHANGED << assets, pState, qrm, qrf, swapGraph, 
                                 ProofPublish, ProofLock, ProofOkRF >>

decisionAbort == /\ pc[CoordinatorID] = "decisionAbort"
                 /\ coordState' = "okRF"
                 /\ ProofOkRF' = TRUE
                 /\ pc' = [pc EXCEPT ![CoordinatorID] = "Done"]
                 /\ UNCHANGED << assets, pState, qrm, qrf, swapGraph, 
                                 ProofPublish, ProofLock, ProofOkRM >>

Coordinator == init_c \/ decision \/ decisionValid \/ decisionAbort

init_src(self) == /\ pc[self] = "init_src"
                  /\ \/ /\ swapGraph = "different" \/ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                     \/ /\ ProofPublish = "true" /\ swapGraph = "correct"
                        /\ pc' = [pc EXCEPT ![self] = "lock"]
                  /\ UNCHANGED << assets, pState, coordState, qrm, qrf, 
                                  swapGraph, ProofPublish, ProofLock, 
                                  ProofOkRM, ProofOkRF >>

lock(self) == /\ pc[self] = "lock"
              /\ IF ProofPublish = "true" /\ self \in Sources /\ assets[AofS(self)] = "OwS"
                    THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "locked"]
                         /\ ProofLock' = [ProofLock EXCEPT ![self] = "true"]
                    ELSE /\ TRUE
                         /\ UNCHANGED << assets, ProofLock >>
              /\ pc' = [pc EXCEPT ![self] = "published"]
              /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                              ProofPublish, ProofOkRM, ProofOkRF >>

published(self) == /\ pc[self] = "published"
                   /\ IF self \in Sources /\ ProofLock[self] = "true" /\ coordState = "published"
                         THEN /\ qrm' = (qrm \union {self})
                         ELSE /\ TRUE
                              /\ qrm' = qrm
                   /\ pc' = [pc EXCEPT ![self] = "waitForD"]
                   /\ UNCHANGED << assets, pState, coordState, qrf, swapGraph, 
                                   ProofPublish, ProofLock, ProofOkRM, 
                                   ProofOkRF >>

waitForD(self) == /\ pc[self] = "waitForD"
                  /\ \/ /\ ProofOkRM = TRUE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED <<assets, qrf>>
                     \/ /\ ProofOkRF = TRUE
                        /\ IF self \in Sources /\ ProofOkRF = TRUE /\ assets[AofS(self)] ="locked"
                              THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "OwS"]
                              ELSE /\ TRUE
                                   /\ UNCHANGED assets
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ qrf' = qrf
                     \/ /\ coordState = "published"
                        /\ IF coordState = "published"
                              THEN /\ qrf' = "true"
                              ELSE /\ TRUE
                                   /\ qrf' = qrf
                        /\ pc' = [pc EXCEPT ![self] = "waitForD"]
                        /\ UNCHANGED assets
                  /\ UNCHANGED << pState, coordState, qrm, swapGraph, 
                                  ProofPublish, ProofLock, ProofOkRM, 
                                  ProofOkRF >>

Source(self) == init_src(self) \/ lock(self) \/ published(self)
                   \/ waitForD(self)

init_bsrc(self) == /\ pc[self] = "init_bsrc"
                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "BdirectToR"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "Bother"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BaskRM"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BlockAsset"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BSaskRF"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BrecoveringAsset"]
                   /\ UNCHANGED << assets, pState, coordState, qrm, qrf, 
                                   swapGraph, ProofPublish, ProofLock, 
                                   ProofOkRM, ProofOkRF >>

BdirectToR(self) == /\ pc[self] = "BdirectToR"
                    /\ IF self \in Sources /\ assets[AofS(self)] = "OwS"
                          THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "OwR"]
                          ELSE /\ TRUE
                               /\ UNCHANGED assets
                    /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                    /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                                    ProofPublish, ProofLock, ProofOkRM, 
                                    ProofOkRF >>

Bother(self) == /\ pc[self] = "Bother"
                /\ IF self \in Sources /\ assets[AofS(self)] = "OwS"
                      THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "other"]
                      ELSE /\ TRUE
                           /\ UNCHANGED assets
                /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                                ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

BaskRM(self) == /\ pc[self] = "BaskRM"
                /\ IF self \in Sources /\ ProofLock[self] = "true" /\ coordState = "published"
                      THEN /\ qrm' = (qrm \union {self})
                      ELSE /\ TRUE
                           /\ qrm' = qrm
                /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                /\ UNCHANGED << assets, pState, coordState, qrf, swapGraph, 
                                ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

BlockAsset(self) == /\ pc[self] = "BlockAsset"
                    /\ IF ProofPublish = "true" /\ self \in Sources /\ assets[AofS(self)] = "OwS"
                          THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "locked"]
                               /\ ProofLock' = [ProofLock EXCEPT ![self] = "true"]
                          ELSE /\ TRUE
                               /\ UNCHANGED << assets, ProofLock >>
                    /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                    /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                                    ProofPublish, ProofOkRM, ProofOkRF >>

BSaskRF(self) == /\ pc[self] = "BSaskRF"
                 /\ IF coordState = "published"
                       THEN /\ qrf' = "true"
                       ELSE /\ TRUE
                            /\ qrf' = qrf
                 /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                 /\ UNCHANGED << assets, pState, coordState, qrm, swapGraph, 
                                 ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

BrecoveringAsset(self) == /\ pc[self] = "BrecoveringAsset"
                          /\ IF self \in Sources /\ ProofOkRF = TRUE /\ assets[AofS(self)] ="locked"
                                THEN /\ assets' = [assets EXCEPT ![AofS(self)] = "OwS"]
                                ELSE /\ TRUE
                                     /\ UNCHANGED assets
                          /\ pc' = [pc EXCEPT ![self] = "init_bsrc"]
                          /\ UNCHANGED << pState, coordState, qrm, qrf, 
                                          swapGraph, ProofPublish, ProofLock, 
                                          ProofOkRM, ProofOkRF >>

BSource(self) == init_bsrc(self) \/ BdirectToR(self) \/ Bother(self)
                    \/ BaskRM(self) \/ BlockAsset(self) \/ BSaskRF(self)
                    \/ BrecoveringAsset(self)

init_rcp(self) == /\ pc[self] = "init_rcp"
                  /\ \/ /\ swapGraph = "different" \/ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                     \/ /\ ProofPublish = "true" /\ swapGraph = "correct"
                        /\ pc' = [pc EXCEPT ![self] = "waitForD_rcp"]
                  /\ UNCHANGED << assets, pState, coordState, qrm, qrf, 
                                  swapGraph, ProofPublish, ProofLock, 
                                  ProofOkRM, ProofOkRF >>

waitForD_rcp(self) == /\ pc[self] = "waitForD_rcp"
                      /\ \/ /\ ProofOkRF = TRUE
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED <<assets, qrf>>
                         \/ /\ ProofOkRM = TRUE
                            /\ IF self \in Recipients /\ ProofOkRM = TRUE /\ assets[AofR(self)] = "locked"
                                  THEN /\ assets' = [assets EXCEPT ![AofR(self)] = "OwR"]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED assets
                            /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ qrf' = qrf
                         \/ /\ coordState = "published"
                            /\ IF coordState = "published"
                                  THEN /\ qrf' = "true"
                                  ELSE /\ TRUE
                                       /\ qrf' = qrf
                            /\ pc' = [pc EXCEPT ![self] = "waitForD_rcp"]
                            /\ UNCHANGED assets
                      /\ UNCHANGED << pState, coordState, qrm, swapGraph, 
                                      ProofPublish, ProofLock, ProofOkRM, 
                                      ProofOkRF >>

Recipient(self) == init_rcp(self) \/ waitForD_rcp(self)

init_brcp(self) == /\ pc[self] = "init_brcp"
                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "BRaskRF"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BRretrievingAsset"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BRdirectToS"]
                      \/ /\ pc' = [pc EXCEPT ![self] = "BRother"]
                   /\ UNCHANGED << assets, pState, coordState, qrm, qrf, 
                                   swapGraph, ProofPublish, ProofLock, 
                                   ProofOkRM, ProofOkRF >>

BRaskRF(self) == /\ pc[self] = "BRaskRF"
                 /\ IF coordState = "published"
                       THEN /\ qrf' = "true"
                       ELSE /\ TRUE
                            /\ qrf' = qrf
                 /\ pc' = [pc EXCEPT ![self] = "init_brcp"]
                 /\ UNCHANGED << assets, pState, coordState, qrm, swapGraph, 
                                 ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

BRretrievingAsset(self) == /\ pc[self] = "BRretrievingAsset"
                           /\ IF self \in Recipients /\ ProofOkRM = TRUE /\ assets[AofR(self)] = "locked"
                                 THEN /\ assets' = [assets EXCEPT ![AofR(self)] = "OwR"]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED assets
                           /\ pc' = [pc EXCEPT ![self] = "init_brcp"]
                           /\ UNCHANGED << pState, coordState, qrm, qrf, 
                                           swapGraph, ProofPublish, ProofLock, 
                                           ProofOkRM, ProofOkRF >>

BRdirectToS(self) == /\ pc[self] = "BRdirectToS"
                     /\ IF self \in Recipients /\ assets[AofR(self)] = "OwR"
                           THEN /\ assets' = [assets EXCEPT ![AofR(self)] = "OwS"]
                           ELSE /\ TRUE
                                /\ UNCHANGED assets
                     /\ pc' = [pc EXCEPT ![self] = "init_brcp"]
                     /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                                     ProofPublish, ProofLock, ProofOkRM, 
                                     ProofOkRF >>

BRother(self) == /\ pc[self] = "BRother"
                 /\ IF self \in Recipients /\ assets[AofR(self)] = "OwR"
                       THEN /\ assets' = [assets EXCEPT ![AofR(self)] = "other"]
                       ELSE /\ TRUE
                            /\ UNCHANGED assets
                 /\ pc' = [pc EXCEPT ![self] = "init_brcp"]
                 /\ UNCHANGED << pState, coordState, qrm, qrf, swapGraph, 
                                 ProofPublish, ProofLock, ProofOkRM, ProofOkRF >>

BRecipient(self) == init_brcp(self) \/ BRaskRF(self)
                       \/ BRretrievingAsset(self) \/ BRdirectToS(self)
                       \/ BRother(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Publisher \/ Coordinator
           \/ (\E self \in CSources: Source(self))
           \/ (\E self \in BSources: BSource(self))
           \/ (\E self \in CRecipients: Recipient(self))
           \/ (\E self \in BRecipients: BRecipient(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Coordinator)
        /\ \A self \in CSources : WF_vars(Source(self))
        /\ \A self \in CRecipients : WF_vars(Recipient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-de2b107e5eaecb3e66e6ef359855b837


(************************* Liveness Property *********************************)
(******************* Checked using Model-Checking ****************************)

AvailableS(a) == assets[a] = "OwS" \/ (ProofOkRF = TRUE /\ assets[a] = "locked")
AvailableR(a) == assets[a] = "OwR" \/ (ProofOkRM = TRUE /\ assets[a] = "locked")
AllParticipantsAreCorrect == (Pi = Pc) /\ swapGraph = "correct"
 
AtLeastOneCorrect == Pc # {} /\ (swapGraph \in SwapStates)
Finish(s,r) == pc[s] = "Done" /\ pc[r] = "Done"
NoCorrect == Pc = {}

(*Theorem IV.9 *)
OwnershipS ==  (\A s \in AssetsFromCS:  AvailableS(s))
OwnershipR ==  (\A r \in AssetsForCR :  AvailableR(r))


Ownership ==   AtLeastOneCorrect => <> (\/ OwnershipS
                                        \/ OwnershipR)
                                      
Ownership2 ==  AtLeastOneCorrect ~> (\/ OwnershipS
                                     \/ OwnershipR)

(*Theorem IV.10 *)
Retrieving == AllParticipantsAreCorrect
               ~> (\A r \in Recipients : assets[AofR(r)]= "OwR")

                    
(*****************************************************************************)
(************************ Consistency property *********************************)

                                                                
Consistency == \A s \in CSources, r \in CRecipients: Finish(s,r) => AvailableS(AofS(s)) \/ AvailableR(AofR(r))
(************************ Safety Property*************************************)
(***********************Proved using TLAPS ***********************************)
                                                                
(* the following is a theorem about all sets of the model that are needed to *)
(* ensure safety of our algorithm.                                           *)

THEOREM SetsTheorem ==
      /\ CoordinatorID # PublisherID
      /\ \A a \in AssetsFromCS : a \in Assets
      /\ \A a \in AssetsForCR : a \in  Assets  
      /\ \A s \in Sources : s \in Pi
      /\ \A r \in Recipients : r \in Pi    
      /\ \A p \in Pc: /\ p \in Pi
                      /\ \/ /\ p \in CSources
                            /\ p \in Sources
                         \/ /\ p \in CRecipients
                            /\ p \in Recipients
                      /\ p \notin BSources 
                      /\ p \notin BRecipients     
      /\ \A s \in CSources : /\ s \in Sources
                             /\ s \in Pi
                             /\ s \in Pc
                             /\ s \notin BSources 
                             /\ s # PublisherID
                             /\ s # CoordinatorID
                             /\ s \notin CRecipients
                             /\ s \notin Recipients
                             /\ s \notin BRecipients
                             /\ AofS(s) \in AssetsFromCS
      /\ \A r \in CRecipients : /\ r \in Recipients
                                /\ r \in Pi
                                /\ r \in Pc
                                /\ r \notin BRecipients
                                /\ r # PublisherID
                                /\ r # CoordinatorID
                                /\ AofR(r) \in AssetsForCR
                                /\ SofA(AofR(r)) \in Sources
      /\ \A bs \in BSources : /\ bs \in Pi
                              /\ bs \in Sources
                              /\ bs \notin CSources
                              /\ bs \notin Pc 
                              /\ bs # PublisherID
                              /\ bs # CoordinatorID
                              /\ AofS(bs) \notin AssetsFromCS
      /\ \A br \in BRecipients: /\ br \in Recipients
                                /\ br \in Pi
                                /\ br \notin Pc 
                                /\ br \notin CRecipients 
                                /\ br # PublisherID
                                /\ br # CoordinatorID 
                                /\ AofR(br) \notin AssetsForCR
      /\ ProcSet = {PublisherID} \cup {CoordinatorID} \cup (CSources) \cup (BSources) \cup (CRecipients) \cup (BRecipients)
      /\ Pi = Sources \cup Recipients
      /\ Pc = Pi \cap Correct
      /\ CSources = Pc \cap Sources
      /\ CRecipients  = Pc \cap Recipients
      /\ BSources  = Sources \ CSources
      /\ BRecipients  = Recipients \ CRecipients
      /\ BSources \cap CSources = {}
      /\ BRecipients \cap CRecipients = {}
      /\ AStates = {"OwS", "OwR", "locked", "other"}
      /\ CStates   = {"init", "published", "okRM", "okRF"}
      /\ PStates   = {"init", "publish"}
      /\ SwapStates  = {"init", "correct", "different"}
      /\ \A s \in Sources: SofA(AofS(s)) = s
      /\ \A s \in Recipients: RofA(AofR(s)) = s
      /\ \A s \in Assets: AofS(SofA(s)) = s
      /\ \A s \in Assets: AofR(RofA(s)) = s
      /\ \A s \in Sources: AofS(s) \in Assets
      /\ \A a \in Assets: SofA(a) \in Sources
BY  DEF ProcSet, CSources, CRecipients, Sources, Recipients, AssetsFromCS, Assets,
AssetsForCR, AofS, AofR, SofA, RofA, Pi, Pc, BSources, BRecipients, PublisherID, CoordinatorID, AStates,
CStates, PStates, SwapStates


(* the following predicate is a type correctness invariant                   *)

TypeOk == /\ assets \in [Assets -> AStates]
          /\ pState \in PStates
          /\ coordState \in CStates
          /\ ProofLock \in [Sources -> { "true", "false" } ]
          /\ ProofPublish \in { "true", "false" }
          /\ ProofOkRM \in BOOLEAN
          /\ ProofOkRF \in BOOLEAN
          /\ qrm \subseteq Sources
          /\ qrf \in { "true", "false" }
          /\ swapGraph \in SwapStates
          /\ pc[CoordinatorID] \in { "init_c", "decision", "decisionValid", "decisionAbort", "Done" }
          /\ pc[CoordinatorID] = "Done" => coordState \in { "okRM", "okRF" }
          /\ pc \in [ ProcSet -> { "init_c", "decision", "decisionValid", "decisionAbort", "Done",
                                   "init_p", "init_src" , "lock", "published", "waitForD", "refunded",  "Done",
                                   "init_bsrc" , "BdirectToR", "Bother", "BaskRM", "BlockAsset", "BSaskRF", "BrecoveringAsset",
                                   "init_rcp" , "waitForD_rcp", "redeemed", "exit_rcp", "Done",
                                   "init_brcp", "BRaskRF", "BRretrievingAsset", "BRdirectToS", "BRother" } ]
          

(*the following predicates are needed to define the coordinator invariant    *)

(*Lemma IV.1*)
init_cInv ==
                                             /\ coordState = "init"
                                             /\ ProofOkRM = FALSE
                                             /\ ProofOkRF = FALSE
                                             /\ ProofPublish = "false"
                                             /\ qrf = "false"
                                             /\ qrm = {}
                                             /\ \A s \in Sources  : /\ ProofLock[s] = "false"
                                             /\ \A s \in CSources  : /\ pc[s] \in {"init_src",  "Done"}
                                                                     /\ ProofLock[s] = "false"
                                                                     /\ assets[AofS(s)] = "OwS"
                                             /\ \A r \in CRecipients  : pc[r] \in {"init_rcp", "Done"}
                                             /\ swapGraph = "init" => pState = "init"
                                             /\ swapGraph ="correct" => pState = "publish"
                                             /\ swapGraph = "different" => pState = "publish"
                                             /\ \A a \in AssetsFromCS: assets[a] = "OwS"
                                             /\ pState = "publish" => pc[PublisherID] = "Done"

(*Lemma IV.2*)
decisionInv ==
                                        /\ coordState = "published"
                                        /\ pState \in {"publish", "Done"}
                                        /\ ProofOkRM = FALSE
                                        /\ ProofOkRF = FALSE
                                        /\ ProofPublish = "true"
                                        /\ pc[PublisherID] = "Done"
                                        /\ \A s \in Sources:
                                              /\ s \in qrm => ProofLock[s] = "true"
                                              /\ ProofLock[s] = "true" => assets[AofS(s)] = "locked"
                                        /\ \A s \in CSources :
                                                        /\ pc[s] \in {"published", "waitForD", "init_src", "lock", "Done"}
                                                        /\ pc[s] \in {"published", "waitForD"}
                                                            => /\ ProofLock[s] = "true"
                                                               /\ assets[AofS(s)] = "locked"
                                                        /\ pc[s] \in {"init_src", "lock", "Done"}
                                                            => /\ ProofLock[s] = "false"
                                                               /\ assets[AofS(s)] = "OwS"
                                                        /\ pc[s] \in {"init_src", "lock", "Done", "published" } => s \notin qrm
                                                        /\ s \in qrm => pc[s] = "waitForD"
                                        /\ \A r \in CRecipients : pc[r] \in {"init_rcp", "waitForD_rcp", "Done"}
                                        /\ \A a \in AssetsFromCS: assets[a] \in {"locked", "OwS"}


decisionValidInv ==
                                        /\ coordState = "published"
                                        /\ pState \in {"publish", "Done"}
                                        /\ ProofOkRM = FALSE
                                        /\ ProofOkRF = FALSE
                                        /\ ProofPublish = "true"
                                        /\ pc[PublisherID] = "Done"
                                        /\ qrm = Sources
                                        /\ \A s \in Sources:
                                              /\ ProofLock[s] = "true"
                                              /\ assets[AofS(s)] = "locked"
                                        /\ \A s \in CSources :
                                                 /\ pc[s] \in {"waitForD"}
                                        /\ \A r \in CRecipients :
                                                 /\ pc[r] \in {"init_rcp", "waitForD_rcp", "Done"}
                                                 /\ assets[AofR(r)] = "locked"
                                                 /\ pc[r] = "init_src" =>  assets[AofR(r)] = "locked"
                                        /\ qrm = Sources => \A a \in Assets : assets[a] = "locked"

decisionAbortInv ==
                                        /\ coordState = "published"
                                        /\ pState \in {"publish", "Done"}
                                        /\ ProofOkRM = FALSE
                                        /\ ProofOkRF = FALSE
                                        /\ ProofPublish = "true"
                                        /\ pc[PublisherID] = "Done"
                                        /\ qrf = "true"
                                        /\ \A s \in CSources :
                                                 /\ assets[AofS(s)] \in { "locked", "OwS" }
                                                 /\ pc[s] \in {"init_src", "lock", "published", "waitForD", "Done"}
                                                 /\ pc[s] = "Done" => assets[AofS(s)] = "OwS"
                                                 /\ pc[s] = "init_src" => assets[AofS(s)] = "OwS"
                                        /\ \A a \in AssetsFromCS: assets[a] \in {"locked", "OwS"}
                                       


(*decisionValidInv /\ okRMInv => Lemma IV.3*)
okRMInv ==                              /\ coordState = "okRM"
                                        /\ ProofOkRM = TRUE
                                        /\ ProofOkRF = FALSE
                                        /\ ProofPublish = "true"
                                        /\ qrm = Sources
                                        /\ pc[PublisherID] = "Done"
                                        /\ \A s \in CSources :
                                            /\ pc[s] \in {"waitForD", "Done"}
                                        /\ \A r \in CRecipients :
                                            /\ pc[r] \in{"init_rcp", "waitForD_rcp", "Done"}
                                            /\ assets[AofR(r)] \in { "locked", "OwR" }
                                            /\ pc[r] = "Done" => assets[AofR(r)] \in {"OwR", "locked"}
                                            /\ pc[r] \in { "init_rcp", "waitForD_rcp"} => assets[AofR(r)] = "locked"
                                            /\ pc[r] = "init_src" => assets[AofR(r)] = "locked"
                                        /\ qrm = Sources => \A a \in AssetsForCR : assets[a] \in {"locked", "OwR"}

(*decisionAbortInv /\ okRFInv => Lemma IV.4*)
okRFInv ==                              /\ ProofOkRM = FALSE
                                        /\ ProofOkRF = TRUE
                                        /\ ProofPublish = "true"
                                        /\ pc[PublisherID] = "Done"
                                        /\ qrf = "true"
                                        /\ \A s \in CSources :
                                             /\ assets[AofS(s)] \in { "locked", "OwS" }
                                             /\ pc[s] = "Done" => assets[AofS(s)] = "OwS"
                                             /\ pc[s] = "init_src" => assets[AofS(s)] = "OwS"
                                        /\ \A a \in AssetsFromCS: assets[a] \in { "locked", "OwS" }



CoordInv2    ==  /\ pc[CoordinatorID] = "init_c" => init_cInv
                 /\ pc[CoordinatorID] = "decision" => decisionInv
                 /\ pc[CoordinatorID] = "decisionValid" => decisionValidInv
                 /\ pc[CoordinatorID] = "decisionAbort" => decisionAbortInv
                 /\ (pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv
                 /\ (pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv
                 
(* the inductive invariant for proving the safety property*) 
Inv == TypeOk  /\ CoordInv2 
   
THEOREM InitImpliesTypeOk ==
    ASSUME Init
    PROVE TypeOk
  <1>1. assets \in [Assets -> AStates]
    BY SetsTheorem DEF TypeOk, Init
  <1>2. pState \in PStates
    BY SetsTheorem DEF TypeOk, Init
  <1>3. coordState \in CStates
    BY SetsTheorem DEF TypeOk, Init
  <1>4. ProofLock \in [Sources -> { "true", "false" } ]
    BY SetsTheorem DEF TypeOk, Init
  <1>5. ProofPublish \in { "true", "false" }
    BY SetsTheorem DEF TypeOk, Init
  <1>6. ProofOkRM \in BOOLEAN
    BY SetsTheorem DEF TypeOk, Init
  <1>7. ProofOkRF \in BOOLEAN
    BY SetsTheorem DEF TypeOk, Init
  <1>8. qrm \subseteq Sources
    BY SetsTheorem DEF TypeOk, Init
  <1>9. qrf \in { "true", "false" }
    BY SetsTheorem DEF TypeOk, Init
  <1>10. swapGraph \in SwapStates
    BY SetsTheorem DEF TypeOk, Init
  <1>11. pc[CoordinatorID] = "Done" => coordState \in { "okRM", "okRF" }
    BY SetsTheorem DEF TypeOk, Init    
  <1>12. pc[CoordinatorID] \in { "init_c", "decision", "decisionValid", "decisionAbort", "Done" }
    BY SetsTheorem DEF TypeOk, Init
  <1>13. pc \in [ ProcSet -> { "init_c", "decision", "decisionValid", "decisionAbort", "Done",
                               "init_p", "init_src" , "lock", "published", "waitForD", "refunded",  "Done",
                               "init_bsrc" , "BdirectToR", "Bother", "BaskRM", "BlockAsset", "BSaskRF", "BrecoveringAsset",
                               "init_rcp" , "waitForD_rcp", "redeemed", "exit_rcp", "Done",
                               "init_brcp", "BRaskRF", "BRretrievingAsset", "BRdirectToS", "BRother" } ]
    BY SetsTheorem DEF TypeOk, Init
  <1>14. QED
    BY <1>1, <1>10, <1>11, <1>12, <1>13, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF TypeOk
 
  
THEOREM InitImpliesCoord ==
    ASSUME TypeOk,
           Init
    PROVE CoordInv2
  BY SetsTheorem DEF TypeOk, Init, CoordInv2, init_cInv
     
THEOREM InitImpliesInv ==
    ASSUME Init
    PROVE TypeOk /\ CoordInv2
BY InitImpliesCoord, InitImpliesTypeOk 

THEOREM TypeOkInvariant ==
    ASSUME TypeOk,
           Next
    PROVE TypeOk'
  <1>1. CASE Publisher
    BY <1>1, SetsTheorem DEF TypeOk, Publisher, init_p
  <1>2. CASE Coordinator
    <2>1. CASE init_c
      BY <2>1, <1>2, SetsTheorem DEF TypeOk, init_c
    <2>2. CASE decision
      BY <2>2, <1>2, SetsTheorem DEF TypeOk, decision
    <2>3. CASE decisionValid
      BY <2>3, <1>2, SetsTheorem DEF TypeOk, decisionValid
    <2>4. CASE decisionAbort
      BY <2>4, <1>2, SetsTheorem DEF TypeOk, decisionAbort
    <2>7. QED
      BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF Coordinator
    
  <1>3. CASE \E self \in CSources: Source(self)
    <2> SUFFICES ASSUME NEW self \in CSources,
                        Source(self)
                 PROVE  TypeOk'
      BY <1>3 
    <2>1. CASE init_src(self)
      BY <2>1, <1>3, SetsTheorem DEF TypeOk, init_src
    <2>2. CASE lock(self)
      BY <2>2, <1>3, SetsTheorem DEF TypeOk, lock
    <2>3. CASE published(self)
      BY <2>3, <1>3, SetsTheorem DEF TypeOk, published
    <2>4. CASE waitForD(self)
      BY <2>4, <1>3, SetsTheorem DEF TypeOk, waitForD
    <2>7. QED
      BY <1>3, <2>1, <2>2, <2>3, <2>4 DEF Source
    
  <1>4. CASE \E self \in BSources: BSource(self)
    <2> SUFFICES ASSUME NEW self \in BSources,
                        BSource(self)
                 PROVE  TypeOk'
      BY <1>4 
    <2>1. CASE init_bsrc(self)
      BY <2>1, <1>4, SetsTheorem DEF TypeOk, init_bsrc
    <2>2. CASE BdirectToR(self)
      BY <2>2, <1>4, SetsTheorem DEF TypeOk, BdirectToR
    <2>3. CASE Bother(self)
      BY <2>3, <1>4, SetsTheorem DEF TypeOk, Bother
    <2>4. CASE BaskRM(self)
      BY <2>4, <1>4, SetsTheorem DEF TypeOk, BaskRM
    <2>5. CASE BlockAsset(self)
      BY <2>5, <1>4, SetsTheorem DEF TypeOk, BlockAsset
    <2>6. CASE BSaskRF(self)
      BY <2>6, <1>4, SetsTheorem DEF TypeOk, BSaskRF
    <2>7. CASE BrecoveringAsset(self)
      BY <2>7, <1>4, SetsTheorem DEF TypeOk, BrecoveringAsset
    <2>8. QED
      BY <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF BSource
    
  <1>5. CASE \E self \in CRecipients: Recipient(self)
    <2> SUFFICES ASSUME NEW self \in CRecipients,
                        Recipient(self)
                 PROVE  TypeOk'
      BY <1>5 
    <2>1. CASE init_rcp(self)
      BY <2>1, <1>5, SetsTheorem DEF TypeOk, init_rcp
    <2>2. CASE waitForD_rcp(self)
      BY <2>2, <1>5, SetsTheorem DEF TypeOk, waitForD_rcp
    <2>5. QED
      BY <1>5, <2>1, <2>2 DEF Recipient
    
  <1>6. CASE \E self \in BRecipients: BRecipient(self)
    <2> SUFFICES ASSUME NEW self \in BRecipients,
                        BRecipient(self)
                 PROVE  TypeOk'
      BY <1>6 
    <2>1. CASE init_brcp(self)
      BY <2>1, <1>6, SetsTheorem DEF TypeOk, init_brcp
    <2>2. CASE BRaskRF(self)
      BY <2>2, <1>6, SetsTheorem DEF TypeOk, BRaskRF
    <2>3. CASE BRretrievingAsset(self)
      BY <2>3, <1>6, SetsTheorem DEF TypeOk, BRretrievingAsset
    <2>4. CASE BRdirectToS(self)
      BY <2>4, <1>6, SetsTheorem DEF TypeOk, BRdirectToS
    <2>5. CASE BRother(self)
      BY <2>5, <1>6, SetsTheorem DEF TypeOk, BRother
    <2>6. QED
      BY <1>6, <2>1, <2>2, <2>3, <2>4, <2>5 DEF BRecipient
    
  <1>7. CASE Terminating
    BY <1>7 DEF TypeOk, Terminating, vars
  <1>8. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next


THEOREM CoordInvariant ==
    ASSUME CoordInv2, TypeOk, TypeOk',
           Next
    PROVE CoordInv2'
  <1>1. CASE pc[CoordinatorID] = "init_c"
    <2>0. init_cInv
      BY <1>1 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>1, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, init_cInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <2>0, <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <2>0, <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv, decisionInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <2>0, <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv                    
        <4>4. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <2>0, <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv                    
        <4>5. ((pc[CoordinatorID] = "Done" /\  coordState="okRM") => okRMInv)'
          BY <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv, CoordInv2
        <4>6. ((pc[CoordinatorID] = "Done" /\  coordState="okRF") => okRFInv)'
          BY <1>1, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c, init_cInv, CoordInv2
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2        
      <3>2. CASE decision
        BY <1>1, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
      <3>3. CASE decisionValid
        BY <1>1, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
      <3>4. CASE decisionAbort
        BY <1>1, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionAbort
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        BY <3>1, <2>0, <1>1, <2>3, SetsTheorem DEF TypeOk, init_src, init_cInv, CoordInv2
      <3>2. CASE lock(self)
        BY <3>2, <2>0, <1>1, <2>3, SetsTheorem DEF TypeOk, lock, init_cInv, CoordInv2
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>1, <2>3, SetsTheorem DEF TypeOk, published, init_cInv, CoordInv2
      <3>4. CASE waitForD(self)
        BY <3>4, <2>0, <1>1, <2>3, SetsTheorem DEF TypeOk, waitForD, init_cInv, CoordInv2
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, init_bsrc, init_cInv, CoordInv2
      <3>2. CASE BdirectToR(self)
        BY <3>2, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, BdirectToR, init_cInv, CoordInv2
      <3>3. CASE Bother(self)
        BY <3>3, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, Bother, init_cInv, CoordInv2
      <3>4. CASE BaskRM(self)
        BY <3>4, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, BaskRM, init_cInv, CoordInv2
      <3>5. CASE BlockAsset(self)
        BY <3>5, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, BlockAsset, init_cInv, CoordInv2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, BSaskRF, init_cInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>1, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, init_cInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>1, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, init_cInv, CoordInv2
      <3>2. CASE waitForD_rcp(self)
        BY <3>2, <1>1, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, init_cInv, CoordInv2
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>1, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, init_cInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>1, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, init_cInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>1, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, init_cInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>1, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, init_cInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5, <1>1, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, init_cInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>1, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, CoordInv2
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    
  <1>2. CASE pc[CoordinatorID] = "decision"
    <2>0. decisionInv
      BY <1>2 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>2, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, decisionInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        BY <1>2, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c        
      <3>2. CASE decision
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision, decisionInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision, decisionInv, ValidTransfer, decisionValidInv
        <4>4. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision, decisionInv, AbortTransfer, decisionAbortInv
        <4>5. ((pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv)'
          BY <2>0, <1>2, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>3. CASE decisionValid
        BY <1>2, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
      <3>4. CASE decisionAbort
        BY <1>2, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionAbort
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        BY <3>1, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, init_src, decisionInv, CoordInv2
      <3>2. CASE lock(self)
        <4>0. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
            BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>2, <2>0, <1>2, <2>3, <4>0, SetsTheorem DEF TypeOk, lock, decisionInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv, decisionValidInv
        <4>4. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv, decisionValidInv
        <4>5. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <3>2, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, lock, decisionInv
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, published, decisionInv, CoordInv2
      <3>4. CASE waitForD(self)
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv, decisionValidInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv, decisionValidInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <3>4, <2>0, <1>2, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionInv
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2        
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, init_bsrc, decisionInv, CoordInv2       
      <3>2. CASE BdirectToR(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "OwR"]
           BY <8>1, <3>2, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>2, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>2, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>3. CASE Bother(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "other"]
           BY <8>1, <3>3, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, Bother, decisionInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>3, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, Bother, decisionInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>3, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, Bother, decisionInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>4. CASE BaskRM(self)
        BY <3>4, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BaskRM, decisionInv, CoordInv2
        
       
      <3>5. CASE BlockAsset(self)
         <8>1. CASE (ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
           BY <8>1, <3>5, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>5, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionInv, CoordInv2
         <8>2. CASE ~(ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
         BY <8>2, <3>5, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BSaskRF, decisionInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>2, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, decisionInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>2, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, decisionInv, CoordInv2
      <3>2. CASE waitForD_rcp(self)
        BY <3>2, <1>2, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionInv, CoordInv2
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>2, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, decisionInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>2, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, decisionInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>2, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, decisionInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>2, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, decisionInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5, <1>2, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, decisionInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>2, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, CoordInv2
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next

  <1>4. CASE pc[CoordinatorID] = "decisionValid"
    <2>0. decisionValidInv
      BY <1>4 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>4, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, decisionValidInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        BY <1>4, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c        
      <3>2. CASE decision
        BY <1>4, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
        
      <3>3. CASE decisionValid
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid, decisionValidInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid, decisionValidInv, okRMInv         
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid, decisionValidInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv)'
          BY <2>0, <1>4, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid, decisionValidInv, okRMInv         
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4,<4>5,<4>6 DEF CoordInv2
      <3>4. CASE decisionAbort
        BY <1>4, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionAbort
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        BY <3>1, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, init_src, decisionValidInv, CoordInv2
      <3>2. CASE lock(self)
        <4>0. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
            BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>2, <2>0, <1>4, <2>3, <4>0, SetsTheorem DEF TypeOk, lock, decisionValidInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv, decisionValidInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv, decisionValidInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <3>2, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, lock, decisionValidInv
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, published, decisionValidInv, CoordInv2
      <3>4. CASE waitForD(self)
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv, decisionValidInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv, decisionValidInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <3>4, <2>0, <1>4, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionValidInv
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2        
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, init_bsrc, decisionValidInv, CoordInv2       
      <3>2. CASE BdirectToR(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "OwR"]
           BY <8>1, <3>2, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionValidInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>2, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionValidInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>2, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionValidInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>3. CASE Bother(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "other"]
           BY <8>1, <3>3, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, Bother, decisionValidInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>3, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, Bother, decisionValidInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>3, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, Bother, decisionValidInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>4. CASE BaskRM(self)
        <4>1. qrm = qrm \union { self }
        BY <3>4, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, decisionValidInv
        <4>2. qrm' = qrm
        BY <4>1 , <3>4 DEF BaskRM
        <4>3. QED
        BY <4>2, <3>4, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BaskRM, decisionValidInv, CoordInv2
        
        
       
      <3>5. CASE BlockAsset(self)
         <8>1. CASE (ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
           BY <8>1, <3>5, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionValidInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>5, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionValidInv, CoordInv2
         <8>2. CASE ~(ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
         BY <8>2, <3>5, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionValidInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BSaskRF, decisionValidInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>4, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, decisionValidInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>4, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, decisionValidInv, CoordInv2
      <3>2. CASE waitForD_rcp(self)
        BY <3>2, <1>4, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionValidInv, CoordInv2
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>4, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, decisionValidInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>4, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, decisionValidInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>4, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, decisionValidInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>4, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, decisionValidInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5, <1>4, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, decisionValidInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>4, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, CoordInv2
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next

  <1>6. CASE pc[CoordinatorID] = "decisionAbort"
    <2>0. decisionAbortInv
      BY <1>6 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>6, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, decisionAbortInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        BY <1>6, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c        
      <3>2. CASE decision
        BY <1>6, <3>2, <2>2, SetsTheorem DEF TypeOk, decision
        
      <3>3. CASE decisionAbort
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort, decisionAbortInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort, decisionAbortInv, okRMInv         
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort, decisionAbortInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv)'
          BY <2>0, <1>6, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionAbort, okRFInv, decisionAbortInv
                   
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4,<4>5,<4>6 DEF CoordInv2
      <3>4. CASE decisionValid
        BY <1>6, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionValid
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>4. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>5. ((pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv)'
          BY <3>1, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, init_src, decisionAbortInv, CoordInv2
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>2. CASE lock(self)
        <4>0. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
            BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>2, <2>0, <1>6, <2>3, <4>0, SetsTheorem DEF TypeOk, lock, decisionAbortInv
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv, decisionAbortInv
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv, decisionAbortInv
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <3>2, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, lock, decisionAbortInv
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, published, decisionAbortInv, CoordInv2
      <3>4. CASE waitForD(self)
        <4>0. pc'[CoordinatorID] = pc[CoordinatorID] /\ pc'[PublisherID] = pc[PublisherID]
          BY <3>4, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, waitForD
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <4>0, <1>6
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <4>0, <1>6
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <4>0, <1>6
        <4>4. ((pc[CoordinatorID] = "Done" /\ coordState="okRM") => okRMInv)'
          BY <4>0, <1>6
        <4>5. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <4>0, <3>4, <2>0, <1>6, <2>3, SetsTheorem DEF TypeOk, waitForD, decisionAbortInv                    
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState="okRF") => okRFInv)'
          BY <4>0, <1>6                    
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2        
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, init_bsrc, decisionAbortInv, CoordInv2       
      <3>2. CASE BdirectToR(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "OwR"]
           BY <8>1, <3>2, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionAbortInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>2, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionAbortInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>2, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BdirectToR, decisionAbortInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>3. CASE Bother(self)
         <8>1. CASE assets[AofS(self)] = "OwS"
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "other"]
           BY <8>1, <3>3, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, Bother, decisionAbortInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>3, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, Bother, decisionAbortInv, CoordInv2
         <8>2. CASE assets[AofS(self)] # "OwS"
         BY <8>2, <3>3, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, Bother, decisionAbortInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>4. CASE BaskRM(self)
        BY <3>4, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BaskRM, decisionAbortInv, CoordInv2
        
        
       
      <3>5. CASE BlockAsset(self)
         <8>1. CASE (ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
           <9>1. assets' = [assets EXCEPT ![AofS(self)] = "locked"]
           BY <8>1, <3>5, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionAbortInv, CoordInv2
           <9>2. QED
           BY <9>1, <8>1, <3>5, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionAbortInv, CoordInv2
         <8>2. CASE ~(ProofPublish = "true" /\ assets[AofS(self)] = "OwS")
         BY <8>2, <3>5, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BlockAsset, decisionAbortInv, CoordInv2
         <8>3. QED
         BY <8>1, <8>2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BSaskRF, decisionAbortInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>6, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, decisionAbortInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, decisionAbortInv, CoordInv2
      <3>2. CASE waitForD_rcp(self)
        <4>1. (pc[CoordinatorID] = "init_c" => init_cInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>2. (pc[CoordinatorID] = "decision" => decisionInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>3. (pc[CoordinatorID] = "decisionValid" => decisionValidInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>4. (pc[CoordinatorID] = "decisionAbort" => decisionAbortInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>5. ((pc[CoordinatorID] = "Done" /\ coordState = "okRM" )  => okRMInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>6. ((pc[CoordinatorID] = "Done" /\ coordState = "okRF" )  => okRFInv)'
          BY <3>2, <1>6, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, decisionAbortInv, CoordInv2
        <4>7. QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF CoordInv2
        
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>6, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, decisionAbortInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>6, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, decisionAbortInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>6, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, decisionAbortInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>6, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, decisionAbortInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5, <1>6, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, decisionAbortInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>6, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, CoordInv2
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next

  <1>3. CASE pc[CoordinatorID] = "Done" /\ coordState = "okRM"
    <2>0. okRMInv
      BY <1>3 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>3, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, okRMInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        BY <1>3, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c        
      <3>2. CASE decision
        BY <1>3, <3>2, <2>2, SetsTheorem DEF TypeOk, decision, CoordInv2
      <3>3. CASE decisionValid
        BY <1>3, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
      <3>4. CASE decisionAbort
        BY <1>3, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionAbort
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        BY <3>1, <2>0, <1>3, <2>3, SetsTheorem DEF TypeOk, init_src, okRMInv, CoordInv2
      <3>2. CASE lock(self)
        BY <3>2, <2>0, <1>3, <2>3, SetsTheorem DEF TypeOk, lock, okRMInv, CoordInv2
        
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>3, <2>3, SetsTheorem DEF TypeOk, published, okRMInv, CoordInv2
      <3>4. CASE waitForD(self)
        BY <3>4, <2>0, <1>3, <2>3, SetsTheorem DEF TypeOk, waitForD, okRMInv, CoordInv2
        
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, init_bsrc, okRMInv, CoordInv2
      <3>2. CASE BdirectToR(self)
        BY <3>2, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, BdirectToR, okRMInv, CoordInv2
      <3>3. CASE Bother(self)
        BY <3>3, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, Bother, okRMInv, CoordInv2
      <3>4. CASE BaskRM(self)
        BY <3>4, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, BaskRM, okRMInv, CoordInv2
        
       
      <3>5. CASE BlockAsset(self)
        BY <3>5, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, BlockAsset, okRMInv, CoordInv2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, BSaskRF, okRMInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>3, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, okRMInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>3, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, okRMInv, CoordInv2        
      <3>2. CASE waitForD_rcp(self)
        BY <3>2, <1>3, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, okRMInv, CoordInv2
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>3, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, okRMInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>3, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, okRMInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>3, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, okRMInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>3, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, okRMInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5,<1>3, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, okRMInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>3, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, vars, CoordInv2, init_cInv, decisionInv,
           okRMInv, decisionValidInv
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next

  <1>5. CASE (pc[CoordinatorID] = "Done" /\ coordState = "okRF")
    <2>0. okRFInv
      BY <1>5 DEF CoordInv2
    <2>1. CASE Publisher
      BY <1>5, <2>0, <2>1, SetsTheorem DEF TypeOk, Publisher, init_p, okRFInv, CoordInv2
    <2>2. CASE Coordinator
      <3>1. CASE init_c
        BY <1>5, <3>1, <2>2, SetsTheorem DEF TypeOk, init_c        
      <3>2. CASE decision
        BY <1>5, <3>2, <2>2, SetsTheorem DEF TypeOk, decision, CoordInv2
      <3>3. CASE decisionValid
        BY <1>5, <3>3, <2>2, SetsTheorem DEF TypeOk, decisionValid
      <3>4. CASE decisionAbort
        BY <1>5, <3>4, <2>2, SetsTheorem DEF TypeOk, decisionAbort
      <3>7. QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF Coordinator
      
    <2>3. CASE \E self \in CSources: Source(self)
      <3> SUFFICES ASSUME NEW self \in CSources,
                          Source(self)
                   PROVE  CoordInv2'
        BY <2>3 
      <3>1. CASE init_src(self)
        BY <3>1, <2>0, <1>5, <2>3, SetsTheorem DEF TypeOk, init_src, okRFInv, CoordInv2
      <3>2. CASE lock(self)
        BY <3>2, <2>0, <1>5, <2>3, SetsTheorem DEF TypeOk, lock, okRFInv, CoordInv2
        
      <3>3. CASE published(self)
        BY <3>3, <2>0, <1>5, <2>3, SetsTheorem DEF TypeOk, published, okRFInv, CoordInv2
      <3>4. CASE waitForD(self)
        BY <3>4, <2>0, <1>5, <2>3, SetsTheorem DEF TypeOk, waitForD, okRFInv, CoordInv2
        
      <3>7. QED
        BY <2>3, <3>1, <3>2, <3>3, <3>4 DEF Source
      
    <2>4. CASE \E self \in BSources: BSource(self)
      <3> SUFFICES ASSUME NEW self \in BSources,
                          BSource(self)
                   PROVE  CoordInv2'
        BY <2>4 
      <3>1. CASE init_bsrc(self)
        BY <3>1, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, init_bsrc, okRFInv, CoordInv2
      <3>2. CASE BdirectToR(self)
        BY <3>2, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, BdirectToR, okRFInv, CoordInv2
      <3>3. CASE Bother(self)
        BY <3>3, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, Bother, okRFInv, CoordInv2
      <3>4. CASE BaskRM(self)
        BY <3>4, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, BaskRM, okRFInv, CoordInv2
        
       
      <3>5. CASE BlockAsset(self)
        BY <3>5, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, BlockAsset, okRFInv, CoordInv2
      <3>6. CASE BSaskRF(self)
        BY <3>6, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, BSaskRF, okRFInv, CoordInv2
      <3>7. CASE BrecoveringAsset(self)
        BY <3>7, <2>0, <1>5, <2>4, SetsTheorem DEF TypeOk, BrecoveringAsset, okRFInv, CoordInv2
      <3>8. QED
        BY <2>4, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEF BSource
      
    <2>5. CASE \E self \in CRecipients: Recipient(self)
      <3> SUFFICES ASSUME NEW self \in CRecipients,
                          Recipient(self)
                   PROVE  CoordInv2'
        BY <2>5 
      <3>1. CASE init_rcp(self)
        BY <3>1, <1>5, <2>0,<2>5, SetsTheorem DEF TypeOk, init_rcp, okRFInv, CoordInv2
      <3>2. CASE waitForD_rcp(self)
        BY <3>2, <1>5, <2>0,<2>5, SetsTheorem DEF TypeOk, waitForD_rcp, okRFInv, CoordInv2
      <3>5. QED
        BY <2>5, <3>1, <3>2 DEF Recipient
      
    <2>6. CASE \E self \in BRecipients: BRecipient(self)
      <3> SUFFICES ASSUME NEW self \in BRecipients,
                          BRecipient(self)
                   PROVE  CoordInv2'
        BY <2>6 
      <3>1. CASE init_brcp(self)
        BY <3>1, <1>5, <2>0,<2>6, SetsTheorem DEF TypeOk, init_brcp, okRFInv, CoordInv2
      <3>2. CASE BRaskRF(self)
        BY <3>2, <1>5, <2>0,<2>6, SetsTheorem DEF TypeOk, BRaskRF, okRFInv, CoordInv2
      <3>3. CASE BRretrievingAsset(self)
        BY <3>3, <1>5, <2>0,<2>6, SetsTheorem DEF TypeOk, BRretrievingAsset, okRFInv, CoordInv2
      <3>4. CASE BRdirectToS(self)
        BY <3>4, <1>5, <2>0,<2>6, SetsTheorem DEF TypeOk, BRdirectToS, okRFInv, CoordInv2
      <3>5. CASE BRother(self)
        BY <3>5, <1>5, <2>0,<2>6, SetsTheorem DEF TypeOk, BRother, okRFInv, CoordInv2
      <3>6. QED
        BY <2>6, <3>1, <3>2, <3>3, <3>4, <3>5 DEF BRecipient
      
    <2>7. CASE Terminating
      BY <1>5, <2>0,<2>7, SetsTheorem DEF TypeOk, Terminating, vars, CoordInv2, init_cInv, decisionInv,
           okRFInv, decisionValidInv
    <2>8. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next

  <1>7. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF TypeOk, CStates

     

THEOREM InvInvariant ==
    ASSUME Inv, Next
    PROVE Inv'
BY TypeOkInvariant, CoordInvariant DEF Inv, TypeOk, CoordInv2, Next

  
THEOREM InvImpliesConsistency ==
    ASSUME TypeOk /\ CoordInv2
    PROVE Consistency
  <1> USE DEF Finish, AvailableS, AvailableR
  <1>1. CASE pc[CoordinatorID] = "init_c"
  BY <1>1, SetsTheorem DEF CoordInv2, init_cInv, Consistency
  <1>2. CASE pc[CoordinatorID] = "decision"
    <2>1. \A a \in AssetsFromCS: assets[a] \in {"locked", "OwS"}
    BY <1>2, SetsTheorem DEF CoordInv2, decisionInv, Consistency  
    <2>2. \A s \in CSources: assets[AofS(s)] \in  {"locked", "OwS"}
    BY <1>2, SetsTheorem DEF CoordInv2, decisionInv, Consistency
    <2>3. \A s \in CSources: pc[s] = "Done" => assets[AofS(s)] = "OwS"
    BY <1>2, SetsTheorem DEF CoordInv2, decisionInv, Consistency
    <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Consistency
  <1>3. CASE pc[CoordinatorID] = "decisionValid"
    <2>1. \A a \in Assets: assets[a] =  "locked"
       BY <1>3, SetsTheorem DEF CoordInv2, decisionValidInv, Consistency 
    <2>2. \A a \in AssetsFromCS: assets[a] = "locked"
       BY <1>3, SetsTheorem DEF CoordInv2, decisionValidInv, Consistency 
    <2>3. \A s \in CSources: pc[s] # "Done" 
       BY <1>3, SetsTheorem DEF  CoordInv2, decisionValidInv, Consistency 
    <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Consistency
  <1>4. CASE  pc[CoordinatorID] = "decisionAbort"
   <2>1. \A a \in AssetsFromCS: assets[a] \in {"locked", "OwS"}
    BY <1>4, SetsTheorem DEF CoordInv2, decisionAbortInv, Consistency
   <2>2. \A s \in CSources: assets[AofS(s)] \in { "locked", "OwS"}
    BY <1>4, SetsTheorem DEF CoordInv2, decisionAbortInv, Consistency
   <2>3. \A s \in CSources: pc[s] = "Done" => assets[AofS(s)] = "OwS"
    BY <1>4, SetsTheorem DEF CoordInv2, decisionAbortInv, Consistency
   <2>4 QED
    BY <2>1, <2>2, <2>3 DEF Consistency
  <1>5. CASE  (pc[CoordinatorID] = "Done" /\ coordState = "okRM" )
    <2>1. ProofOkRM = TRUE  => \A a \in AssetsForCR: assets[a] \in {"locked", "OwR"}
    BY <1>5, SetsTheorem DEF CoordInv2, okRMInv, Consistency 
    <2>2. \A r \in CRecipients : pc[r] = "Done" => assets[AofR(r)] \in {"OwR", "locked"}
    BY <1>5, SetsTheorem DEF CoordInv2, okRMInv, Consistency 
    <2>3. ProofOkRM = TRUE 
    BY <1>5, SetsTheorem DEF CoordInv2, okRMInv, Consistency 
   <2>4 QED
    BY <2>1, <2>2, <2>3 DEF Consistency
  <1>6. CASE  (pc[CoordinatorID] = "Done" /\ coordState = "okRF" )
   <2>1. \A a \in AssetsFromCS: assets[a] \in {"locked", "OwS"}
    BY <1>6, SetsTheorem DEF CoordInv2, okRFInv, Consistency
   <2>2. \A s \in CSources: pc[s] = "Done"  => assets[AofS(s)] = "OwS"
    BY <1>6, SetsTheorem DEF CoordInv2, okRFInv, Consistency
   <2>3 QED
    BY <2>1, <2>2 DEF Consistency
  <1>7. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF TypeOk


THEOREM Safety2 == Spec => [] Consistency
<1>1. Init => Inv
  BY InitImpliesInv, SMT DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    BY <2>1, SMTT(60), InvInvariant DEF vars
  <2>2. CASE UNCHANGED vars
    BY <2>2, SMTT(60) DEF vars, Inv, TypeOk, CoordInv2, okRFInv, 
    okRMInv, decisionAbortInv, decisionValidInv, init_cInv, decisionInv
  <2>3. QED
    BY <2>1, <2>2
  
<1>3. Inv => Consistency
  BY SMT, InvImpliesConsistency DEFS Consistency, Inv 
<1>4. QED
  BY ONLY <1>1,<1>2,<1>3,PTL DEF Spec



    


=============================================================================
