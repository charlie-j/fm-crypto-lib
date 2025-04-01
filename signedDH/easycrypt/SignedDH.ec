require import AllCore Real FMap FSet Distr.
require import PROM.

require (*--*) StdOrder.
(*---*) import StdOrder.RealOrder.

require (*--*) St_CDH_abstract SUFCMA UATPaKE.

(** Buckle Up! **)
(* Starting notes:
   - We (try to) follow Doreen and Paul's model as closely as possible
     while remaining precise.
   - The NIKE is split out as Nominal Group with Gap-DH + RO. The
     entire scheme could be proved assuming an abstract NIKE (with
     m-CKS-heavy security), and that be constructed from NG + Gap-DH +
     RO.
*)

(** Types and operators for the DH group **)
type pdh, sdh, sskey.

op g: pdh.
op [lossless] dsk: sdh distr.
op (^): pdh -> sdh -> pdh.

axiom shared_keyC x y:
     x \in dsk
  => y \in dsk
  => (g ^ x) ^ y = (g ^ y) ^ x.

op [lossless full uniform] dssk: sskey distr.

(** Instantiate the GapDH theory **)
clone import St_CDH_abstract as StCDH with
  type pkey <= pdh,
  type skey <= sdh,
  op   g    <= g,
  op   dsk  <= dsk,
  op   (^)  <= (^)
proof *.
realize dsk_ll by exact: dsk_ll.
realize shared_keyC by exact: shared_keyC.

(** Additional types for the signature scheme **)
type pkey, skey, sig.

(** Instantiate the UFCMA theory **)
clone import SUFCMA as Signature with
  type pkey   <= pkey,
  type skey   <= skey,
  type sig    <= sig,
  type msg    <= pdh * pdh
proof *.

(** Additional types for defining protocols,
    plus RO instantiation
**)
type client_state = { pk: pkey;     (* The server's identity, as its public key *)
                      epk: pdh;     (* The client's ephemeral public key *)
                      esk: sdh   }. (* The client's ephemeral secret *)

clone import FullRO as H with
  type in_t    <= pdh * pdh * pdh,
  type out_t   <= sskey,
  op   dout  _ <= dssk,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

(** Instantiate the ProtRO theory **)
clone import UATPaKE as Security with
  type pkey         <= pkey,
  type skey         <= skey,
  type sskey        <= sskey,
  op   dssk         <= dssk,
  type client_state <= client_state,
  type msg1         <= pdh,
  type msg2         <= pdh * sig,
  type ro_in        <= pdh * pdh * pdh,
  type ro_out       <= sskey,
  op   d_ro         <= Self.dssk
proof *.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Finally, we define the signed DH protocol **)
module SignedDH (S : SigScheme) (H : RO) : UATPaKE = {
  proc gen() = {
    var kp;

    kp <@ S.keygen();
    return kp;
  }

  proc init(pk) = {
    var x_sk;

    x_sk <$ dsk;
    return ({| pk = pk; epk = g ^ x_sk; esk = x_sk |}, g ^ x_sk);
  }

  proc resp(sk_s, x_pk) = {
    var y_sk, s, ks;

    y_sk <$ dsk;
    s <@ S.sign(sk_s, (x_pk, g ^ y_sk));
    ks <@ H.get(x_pk, g ^ y_sk, x_pk ^ y_sk);
    return (ks, (g ^ y_sk, s));
  }

  proc recv(st, c) = {
    var y_pk, s, b, kc;
    var r <- None;

    (y_pk, s) <- c;
    b <@ S.verify(st.`pk, (st.`epk,  y_pk), s);
    if (b) {
      kc <@ H.get(st.`epk, y_pk, y_pk ^ st.`esk);
      r <- Some kc;
    }
    return r;
  }
}.

module B2 (S : SigScheme) (A : Adv_UATPaKE_RO) (O : St_CDH_Oracles) = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var h_map : (pdh option * pdh * pdh, sskey) fmap

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var k, ko, b;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        b <@ O.ddh(x, y, z);
        if (has (fun _ c=> c = x) i_map /\ b) {
          k <@ h'(x, y);
          ko <- Some k;
        } else {
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }
      
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var pk, x;
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        pk <- (oget c_map.[i]).`pk;
        x <@ O.corrupt_1(i);
        r <- Some {| pk = pk; epk = g ^ oget x; esk = oget x |};
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c, epk;

      n <- n + 1;
      epk <@ O.gen_1();
      st <- {| pk = pk; epk = epk; esk = witness; |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          h <@ O.gen_2();
        } else {
          y <$ dsk;
          h <- g ^ y;
        }
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          k <@ h'(c, h);
        } else {
          k <@ RO.get(c, h, c ^ y);
        }
        c' <- (h, sig);
        io <- find (fun i j' => j' = j /\ i_map.[i] = Some c) p_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            (* Spec says "Stop" *)
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc solve() = {
    var b';

    RO.init();

    b_ror <- witness;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    h_map <- empty;

    b' <@ A(Oracles).distinguish();
  }
}.

section.
declare module S <: SigScheme { -Exp_b, -RO }.
declare module A <: Adv_UATPaKE_RO { -Exp_b, -RO, -S }.

local module Game0_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      m <- m + 1;
      (pk, sk) <@ S.keygen();
      pk_map.[m] <- pk;
      sk_map.[m] <- sk;
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, x, c;

      n <- n + 1;
      x <$ dsk;
      c <- g ^ x;
      st <- {| pk = pk; epk = c; esk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c, h, c ^ y);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h = RO.get
  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

local lemma Hop0 &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m: res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true ) @ &m: res] |
  = `|  Pr[Game0_b.run(false) @ &m: res]
      - Pr[Game0_b.run(true ) @ &m: res] |.
proof.
have ^ + -> - -> //:
  forall b, Pr[Exp_b(SignedDH(S), RO, A).run(b) @ &m: res]
          = Pr[Game0_b.run(b) @ &m: res].
move=> b; byequiv (: ={glob A, glob S, arg} ==> ={res})=> //.
proc.
(* The calls are equivalent due to equality on a bunch of variables *)
call (: ={glob Exp_b(SignedDH(S), RO)}); last first.
(* The invariant holds initially and allows us to conclude *)
+ by inline *; auto.
(* The invariant is preserved by all oracles *)
+ by proc; inline *; auto; call (: true); auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ by proc; inline *; sim; auto.
+ proc; inline *; sp; if; auto.
  sim; auto.
  by call (: true); auto.
+ proc; sp; if; auto; sp; if; auto.
  inline {1} 1.
  by sim; auto.
+ conseq (: _ ==> ={glob RO, res})=> //.
  by sim.
qed.


local module Game1_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var bad_1: bool
  var bad_2: bool

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;
  
      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Pen and paper says "Stop" *)
        (* Here, we don't stop; we just don't actually register the key and move on *)
        (* The only thing we care about is the rest of the proof,
           where we want to rely on the fact that each client instance
           has at most one intended honest partner
        *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }
  
    proc corrupt(j: int): skey option = {
      var r <- None;
  
      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }
  
    proc expose(i) = {
      var r <- None;
  
      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }
  
    proc init(pk: pkey): pdh = {
      var st, jo, c, x;
  
      n <- n + 1;
      x <$ dsk;
      c <- g ^ x;
      st <- {| pk = pk; epk = c; esk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }
  
    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;
  
      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c, h, c ^ y);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }
  
    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;
  
      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }
  
    proc h = RO.get
  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

(* In order to get the absolute values in, we need to make sure that
   we can express the bad event on the left of the hop. While we do
   this, we also set things up nicely to avoid having to reason about
   equivalence up to bad in manual mode.
*)
local module Game05_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]

  module Oracles = {
    (* The oracles are unchanged from Game1, except for gen *)
    include Game1_b.Oracles [-gen]

    proc gen(): pkey = {
      var pk, sk;
  
      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }
  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

(** Despite setting things up, the syntactic 'equivalent up to' tactic
    is failing here for some reason. So we must do it by hand, which
    requires us assuming that the adversary and the signature scheme
    terminate.

    This can pop off once the bugs in `byupto` are fixed.
**)
(* For all oracles that terminate, the adversary terminates *)
declare axiom A_ll (O <: UATPaKE_RO_Oracles {-A}):
     islossless O.gen
  => islossless O.corrupt
  => islossless O.expose
  => islossless O.init
  => islossless O.respond
  => islossless O.receive
  => islossless O.h
  => islossless A(O).distinguish.

declare axiom S_keygen_ll: islossless S.keygen.
declare axiom S_sign_ll: islossless S.sign.
declare axiom S_verify_ll: islossless S.verify.

local lemma Hop1 (b : bool) &m:
  `|Pr[Game0_b.run(b) @ &m: res] - Pr[Game1_b.run(b) @ &m: res]|
  <= Pr[Game1_b.run(b) @ &m: Game1_b.bad_1].
proof.
(* We need to make the bad event appear in the left game for the
   absolute value to work out; this is just a pure equivalence
   with a bit of a twist, since we modify *one* of the oracles
   to branch on the failure event and set bad, but without changing
   its obserable behaviour. The proof quickly focuses on this. *)
have ->: Pr[Game0_b.run(b) @ &m: res] = Pr[Game05_b.run(b) @ &m: res].
+ byequiv (: ={glob A, glob S, b} ==> ={res})=> //; proc.
  call (: ={glob Exp_b, glob S, glob RO}); [2..7:by sim|8:by inline; auto].
  by proc; auto; call (: true); auto=> />.
(* Now, in theory, this could be done by the syntactic check: those
   two games are syntactically equal except in branches that set bad
   to true. However, this is borked right now, so we breathe in manual
   mode, and we prove _semantically_ that:
   1. Some invariant holds until bad happens, and implies the desired
   equality of events in final memories;
   2. Bad happens on both sides at the same time.
*)
byequiv: Game1_b.bad_1=> [||/#] //.
proc.
(* And now we lift the reasoning up to bad to the oracles the
   adversary has access to. Because we're in manual mode, and the
   semantics of `equiv` imply equitermination, we *must* also show that
   everything terminates once bad has occurred (we can no longer rely on
   the relational reasoning to guarantee thise once the programs are out
   of sync). In addition, and perhaps obviously, we must prove that
   the bad even can never unhappen once it has happened.  Keep in mind
   that it is simply a property of the state (here, the value of a
   boolean variable), and that the state can be modified
   programmatically. It isn't some external, untouchable truth. *)
call (: Game1_b.bad_1 (* the bad event *)
      , ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2} (* the invariant that holds until bad happens *)
      , ={Game1_b.bad_1}). (* the invariant that holds after bad happens *)
(* Goal 1: the adversary terminates if its oracles terminate. See above. *)
+ exact: A_ll.
(* Goal i.0: if bad does not hold, and the non-bad invariant holds
   initially, then executing the oracles leads us to memories that are
   such that the correct invariant holds (depending on whether bad
   happened during the oracles' execution *)
+ by proc; auto; call (: true); auto.
(* Goal i.1: the left-hand side oracle terminates and preserves bad *)
+ move=> &2 bad; proc; auto=> />.
  by call S_keygen_ll; auto=> />; rewrite bad.
(* Goal i.2: the right-hand side oracle terminates and preserves bad *)
+ move=> &1; proc; auto.
  by call S_keygen_ll; auto=> />.
(* Do those three again for all oracles *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; proc; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ move=> &1; proc; auto=> /> &0.
  by rewrite dsk_ll /= /#.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ move=> &1; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  exact: S_verify_ll.
+ move=> &1; conseq (: true); proc; islossless.
  exact: S_verify_ll.
(* And again *)
+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, Game1_b.bad_2, res})=> //.
  by sim.
+ by move=> &2 bad; conseq (: true); proc; islossless.
+ by move=> &1; conseq (: true); proc; islossless.
(* Finally, show that the invariant implies what we wanted (and that
   the program's preamble establishes the invariant) *)
by inline; auto=> /> /#.
qed.

local module Game2_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Here, we don't stop; we just don't actually register the key and move on *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c, x;

      n <- n + 1;
      x <$ dsk;
      c <- g ^ x;
      st <- {| pk = pk; epk = c; esk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c, h, c ^ y);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(st_i.`epk, h, h ^ st_i.`esk);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_2 <- true;
            ko <- None;
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h = RO.get
  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

local lemma Hop2 b &m:
  `|Pr[Game1_b.run(b) @ &m: res] - Pr[Game2_b.run(b) @ &m: res]|
  <= Pr[Game2_b.run(b) @ &m: Game1_b.bad_2].
admitted.

local module Game3_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]

  var h_map : (pdh option * pdh * pdh, sskey) fmap

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var io, st_i, k, ko;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        io <- find (fun _ c=> c = x) i_map;
        if (io is Some i) {
          st_i <- oget c_map.[i];
          if (z = y ^ st_i.`esk) {
            k <@ h'(x, y);
            ko <- Some k;
          }
        }
        if (ko is None) {
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }
      
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Here, we don't stop; we just don't actually register the key and move on *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }
      
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        r <- sk_map.[j];
        cr <- cr `|` fset1 j;
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var st, jo, c, x;

      n <- n + 1;
      x <$ dsk;
      c <- g ^ x;
      st <- {| pk = pk; epk = c; esk = x |};
      c_map.[n] <- st;
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        sk_j <- oget sk_map.[j];
        y <$ dsk;
        h <- g ^ y;
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        if (has (fun i c' => c' = c) i_map) {
          k <@ h'(c, h);
        } else {
          k <@ RO.get(c, h, c ^ y);
        }
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;
        
        if (c \notin odflt fset0 r_map.[p_map.[i], i]) {
          (h, sig) <- c;
          b <@ S.verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_2 <- true;
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc run(b) = {
    var b';

    RO.init();

    b_ror <- b;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    p_map <- empty;
    i_map <- empty;
    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    h_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

op p: real.
local lemma Hop3 b &m:
  `|Pr[Game2_b.run(b) @ &m: res] - Pr[Game3_b.run(b) @ &m: res]|
  <= p.
admitted.

local lemma Reduction &m:
  `|Pr[Game3_b.run(false) @ &m: res] - Pr[Game3_b.run(true) @ &m: res]|
  <= Pr[St_CDH(B2(S,A)).run() @ &m: res].
proof. admitted.

local lemma Security_of_SignedDH &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m : res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true) @ &m : res]|
  <=   Pr[Game1_b.run(true) @ &m: Game1_b.bad_1]
     + Pr[Game1_b.run(false) @ &m: Game1_b.bad_1]
     + Pr[Game2_b.run(true) @ &m : Game1_b.bad_2]
     + Pr[Game2_b.run(false) @ &m : Game1_b.bad_2]
     + 2%r * p
     + Pr[St_CDH(B2(S,A)).run() @ &m: res].
proof.
smt(Hop0 Hop1 Hop2 Hop3 Reduction).
qed.
end section.
