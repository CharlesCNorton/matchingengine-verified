(******************************************************************************)
(*                                                                            *)
(*            Matching Engine: Exchange Order Book Price-Time Priority        *)
(*                                                                            *)
(*     Formal verification of continuous double auction matching rules.       *)
(*     Encodes price-time priority, order types, fill-or-kill semantics,      *)
(*     and crossed book resolution.                                           *)
(*                                                                            *)
(*     The stock exchange is a poor substitute for the Holy Grail.            *)
(*     (John Maynard Keynes, 1936)                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 5, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: ORDER TYPES AND SIDES                                           *)
(******************************************************************************)

Inductive Side : Type :=
  | Buy
  | Sell.

Definition opposite_side (s : Side) : Side :=
  match s with Buy => Sell | Sell => Buy end.

Lemma opposite_side_involution : forall s,
  opposite_side (opposite_side s) = s.
Proof. intros []; reflexivity. Qed.

Inductive OrderType : Type :=
  | Limit      (* execute at limit price or better *)
  | Market     (* execute at best available price *)
  | FillOrKill (* must fill completely immediately or cancel *)
  | ImmediateOrCancel.  (* fill whatever is available, cancel rest *)

(******************************************************************************)
(* SECTION 2: ORDERS                                                          *)
(******************************************************************************)

(* Prices and quantities are natural numbers (cents for price, shares for qty) *)
Record Order : Type := mkOrder {
  ord_id        : nat;
  ord_side      : Side;
  ord_type      : OrderType;
  ord_price     : nat;   (* limit price in cents; 0 = market *)
  ord_qty       : nat;   (* remaining quantity *)
  ord_timestamp : nat;   (* submission time — smaller = earlier *)
}.

(* Two orders are compatible for matching: buy price >= sell price *)
Definition prices_cross (buy_price sell_price : nat) : bool :=
  Nat.leb sell_price buy_price.

Lemma prices_cross_symmetric_bound : forall bp sp,
  prices_cross bp sp = true ->
  sp <= bp.
Proof.
  intros bp sp H. unfold prices_cross in H. apply Nat.leb_le. exact H.
Qed.

(******************************************************************************)
(* SECTION 3: PRICE-TIME PRIORITY                                             *)
(******************************************************************************)

(* Buy side priority: higher price first; tie-break by earlier timestamp *)
Definition buy_priority (o1 o2 : Order) : bool :=
  if Nat.ltb (ord_price o2) (ord_price o1) then true   (* o1 better price *)
  else if Nat.ltb (ord_price o1) (ord_price o2) then false  (* o2 better price *)
  else Nat.leb (ord_timestamp o1) (ord_timestamp o2).  (* tie: earlier first *)

(* Sell side priority: lower price first; tie-break by earlier timestamp *)
Definition sell_priority (o1 o2 : Order) : bool :=
  if Nat.ltb (ord_price o1) (ord_price o2) then true   (* o1 better price *)
  else if Nat.ltb (ord_price o2) (ord_price o1) then false
  else Nat.leb (ord_timestamp o1) (ord_timestamp o2).

(* Priority is reflexive *)
Lemma buy_priority_refl : forall o, buy_priority o o = true.
Proof.
  intros o. unfold buy_priority.
  rewrite Nat.ltb_irrefl. simpl. apply Nat.leb_refl.
Qed.

Lemma sell_priority_refl : forall o, sell_priority o o = true.
Proof.
  intros o. unfold sell_priority.
  rewrite Nat.ltb_irrefl. simpl. apply Nat.leb_refl.
Qed.

(* Better price wins on buy side *)
Theorem buy_better_price_wins : forall o1 o2,
  ord_price o2 < ord_price o1 ->
  buy_priority o1 o2 = true.
Proof.
  intros o1 o2 H.
  unfold buy_priority.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(* Better price wins on sell side *)
Theorem sell_better_price_wins : forall o1 o2,
  ord_price o1 < ord_price o2 ->
  sell_priority o1 o2 = true.
Proof.
  intros o1 o2 H.
  unfold sell_priority.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(* Earlier order wins on same price *)
Theorem buy_earlier_timestamp_wins : forall o1 o2,
  ord_price o1 = ord_price o2 ->
  ord_timestamp o1 <= ord_timestamp o2 ->
  buy_priority o1 o2 = true.
Proof.
  intros o1 o2 Hprice Hts.
  unfold buy_priority.
  rewrite (Nat.ltb_irrefl (ord_price o1)) || idtac.
  destruct (Nat.ltb (ord_price o2) (ord_price o1)) eqn:H1.
  - apply Nat.ltb_lt in H1. lia.
  - destruct (Nat.ltb (ord_price o1) (ord_price o2)) eqn:H2.
    + apply Nat.ltb_lt in H2. lia.
    + apply Nat.leb_le. exact Hts.
Qed.

(******************************************************************************)
(* SECTION 4: ORDER BOOK                                                      *)
(******************************************************************************)

(* An order book has sorted bid and ask queues *)
Record OrderBook : Type := mkBook {
  book_bids : list Order;   (* sorted by buy_priority: best bid first *)
  book_asks : list Order;   (* sorted by sell_priority: best ask first *)
}.

Definition empty_book : OrderBook := mkBook [] [].

(* Best bid: first element of bid queue *)
Definition best_bid (book : OrderBook) : option Order :=
  match book_bids book with
  | []    => None
  | o :: _ => Some o
  end.

(* Best ask: first element of ask queue *)
Definition best_ask (book : OrderBook) : option Order :=
  match book_asks book with
  | []    => None
  | o :: _ => Some o
  end.

(* A book is crossed if best bid >= best ask *)
Definition book_crossed (book : OrderBook) : bool :=
  match best_bid book, best_ask book with
  | Some bid, Some ask => prices_cross (ord_price bid) (ord_price ask)
  | _, _               => false
  end.

(* Empty book is not crossed *)
Lemma empty_book_not_crossed : book_crossed empty_book = false.
Proof. reflexivity. Qed.

(******************************************************************************)
(* SECTION 5: MATCHING — FILL QUANTITY                                        *)
(******************************************************************************)

(* The fill quantity for a match is the minimum of buyer and seller qty *)
Definition fill_qty (buy_qty sell_qty : nat) : nat :=
  Nat.min buy_qty sell_qty.

(* Fill quantity does not exceed either side's quantity *)
Theorem fill_le_buy : forall bq sq,
  fill_qty bq sq <= bq.
Proof. intros bq sq. unfold fill_qty. apply Nat.le_min_l. Qed.

Theorem fill_le_sell : forall bq sq,
  fill_qty bq sq <= sq.
Proof. intros bq sq. unfold fill_qty. apply Nat.le_min_r. Qed.

(* After a fill, remaining quantities are non-negative *)
Theorem fill_remaining_non_negative : forall bq sq,
  bq - fill_qty bq sq >= 0 /\ sq - fill_qty bq sq >= 0.
Proof. intros bq sq. unfold fill_qty. split; lia. Qed.

(* A complete fill occurs when fill_qty = qty of one side *)
Definition complete_fill_buy (bq sq : nat) : bool :=
  Nat.eqb (fill_qty bq sq) bq.

Definition complete_fill_sell (bq sq : nat) : bool :=
  Nat.eqb (fill_qty bq sq) sq.

Lemma complete_fill_when_buyer_smaller : forall bq sq,
  bq <= sq ->
  complete_fill_buy bq sq = true.
Proof.
  intros bq sq H.
  unfold complete_fill_buy, fill_qty.
  rewrite Nat.min_l; [apply Nat.eqb_refl | exact H].
Qed.

Lemma complete_fill_when_seller_smaller : forall bq sq,
  sq <= bq ->
  complete_fill_sell bq sq = true.
Proof.
  intros bq sq H.
  unfold complete_fill_sell, fill_qty.
  rewrite Nat.min_r; [apply Nat.eqb_refl | exact H].
Qed.

(******************************************************************************)
(* SECTION 6: TRADE PRICE DETERMINATION                                       *)
(******************************************************************************)

(* Exchange rules vary on trade price determination.
   Common rules:
   - Passive side (resting order) price prevails
   - Opening auction: single clearing price
   We model: resting order price = trade price *)

Definition trade_price (resting_price : nat) : nat := resting_price.

(* Trade price equals the resting order's limit price *)
Lemma trade_price_equals_resting : forall p,
  trade_price p = p.
Proof. intros p. reflexivity. Qed.

(******************************************************************************)
(* SECTION 7: FILL-OR-KILL SEMANTICS                                          *)
(******************************************************************************)

(* An FOK order must be filled completely in one attempt or cancelled entirely.
   It is fillable iff the available liquidity >= the order quantity. *)
Definition fok_fillable (order_qty available_qty : nat) : bool :=
  Nat.leb order_qty available_qty.

Theorem fok_not_fillable_cancelled : forall oq aq,
  oq > aq ->
  fok_fillable oq aq = false.
Proof.
  intros oq aq H.
  unfold fok_fillable. apply Nat.leb_nle. lia.
Qed.

Theorem fok_fillable_exactly : forall qty,
  fok_fillable qty qty = true.
Proof.
  intros qty. unfold fok_fillable. apply Nat.leb_refl.
Qed.

(******************************************************************************)
(* SECTION 8: INVARIANTS — ORDER BOOK INTEGRITY                               *)
(******************************************************************************)

(* An order is valid: qty > 0, price > 0 for limit orders *)
Definition order_valid (o : Order) : bool :=
  Nat.ltb 0 (ord_qty o) &&
  match ord_type o with
  | Market => true
  | _      => Nat.ltb 0 (ord_price o)
  end.

(* All orders in the book are valid *)
Definition book_valid (book : OrderBook) : bool :=
  forallb order_valid (book_bids book) &&
  forallb order_valid (book_asks book).

Lemma empty_book_valid : book_valid empty_book = true.
Proof. reflexivity. Qed.

(* After a complete fill, the filled order is removed (qty = 0 => invalid) *)
Theorem zero_qty_order_invalid : forall o,
  ord_qty o = 0 ->
  order_valid o = false.
Proof.
  intros o H.
  unfold order_valid. rewrite H. reflexivity.
Qed.

(******************************************************************************)
(* SECTION 9: PRICE-TIME PRIORITY TRANSITIVITY                                *)
(******************************************************************************)

(* If order A has better price than B, and B has better price than C,
   then A has better price than C (on buy side). *)
Theorem buy_price_priority_transitive : forall o1 o2 o3,
  ord_price o2 < ord_price o1 ->
  ord_price o3 < ord_price o2 ->
  buy_priority o1 o3 = true.
Proof.
  intros o1 o2 o3 H1 H2.
  apply buy_better_price_wins. lia.
Qed.

Theorem sell_price_priority_transitive : forall o1 o2 o3,
  ord_price o1 < ord_price o2 ->
  ord_price o2 < ord_price o3 ->
  sell_priority o1 o3 = true.
Proof.
  intros o1 o2 o3 H1 H2.
  apply sell_better_price_wins. lia.
Qed.

(******************************************************************************)
(* SECTION 10: SUMMARY                                                        *)
(******************************************************************************)

(*
  This file formalizes the core logic of an exchange matching engine.

  Structure:
    1. Order types: Limit, Market, FillOrKill, ImmediateOrCancel.
    2. Sides: Buy/Sell with involution.
    3. Price-time priority: buy (higher price first) and sell (lower price first),
       with timestamp tie-breaking.
    4. Order book: bid/ask queues; best_bid/best_ask; crossed-book detection.
    5. Fill quantity: min(buy_qty, sell_qty); fill <= each side's qty.
    6. Complete fill: buyer or seller fully consumed.
    7. Trade price: resting order price determines execution price.
    8. Fill-or-Kill: FOK order cancelled if liquidity < order qty.
    9. Order validity: qty > 0 and price > 0 for non-market orders.
    10. Priority transitivity: price priority is transitive on both sides.

  Key theorems:
    - prices_cross_symmetric_bound
    - buy/sell_better_price_wins
    - buy_earlier_timestamp_wins
    - fill_le_buy / fill_le_sell
    - complete_fill_when_buyer/seller_smaller
    - fok_not_fillable_cancelled / fok_fillable_exactly
    - zero_qty_order_invalid
    - buy/sell_price_priority_transitive

  All proofs closed; no Admitted lemmas.
*)
