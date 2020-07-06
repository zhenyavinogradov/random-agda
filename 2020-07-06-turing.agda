module _ where

module Lib where
  infixl 10 _+_
  data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  infixr 15 _×_
  infixr 5 _,_
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _×_ public

  mutual
    data DelayF (A : Set) : Set where
      now   : A → DelayF A
      later : Delay A → DelayF A

    record Delay (A : Set) : Set where
      coinductive
      field forceDelay : DelayF A
  open Delay public

  record Stream (A : Set) : Set where
    coinductive
    constructor mkStream
    field forceStream : A × Stream A
  open Stream public
  
  head : {A : Set} → Stream A → A
  head s = fst (forceStream s)

  tail : {A : Set} → Stream A → Stream A
  tail s = snd (forceStream s)

  consStream : {A : Set} → A → Stream A → Stream A
  consStream a s = mkStream (a , s)
open Lib public


postulate
  Symbol : Set         -- symbols on the tape
  emptySymbol : Symbol -- initial symbol
  Result : Set         -- result returned by a turing machine when it halts


-- tape
module _ where
  data Tape : Set where
    mkTape : (left : Stream Symbol) → (current : Symbol) → (right : Stream Symbol) → Tape

  -- Move to the left
  #left : Tape → Tape
  #left (mkTape l c r) = mkTape (tail l) (head l) (consStream c r)
  
  -- Move to the right
  #right : Tape → Tape
  #right (mkTape l c r) = mkTape (consStream c l) (head r) (tail r)
  
  -- Replace current cell
  #write : Symbol → Tape → Tape
  #write c' (mkTape l _ r) = mkTape l c' r
  
  -- Get current cell
  #read : Tape → Symbol
  #read (mkTape _ c _) = c


-- turing machine interpreter
module _ where
  -- Turing machine code
  data TM : Set where
    $left  : (cont : TM) → TM                      -- move to the left
    $right : (cont : TM) → TM                      -- move to the right
    $write : (symbol : Symbol) → (cont : TM) → TM  -- write to the current cell
    $read  : (cont : Symbol → TM) → TM             -- read from the current cell
    $halt  : (result : Result) → TM                -- finish

  -- Current code and current tape state
  State : Set
  State = TM × Tape

  -- Single computation step. Returns a result if computation finishes, or next state if it doesn't
  step : State → Result + State
  step ($left cont , tape)         = inr (cont , #left tape)
  step ($right cont , tape)        = inr (cont , #right tape)
  step ($write symbol cont , tape) = inr (cont , #write symbol tape)
  step ($read cont , tape)         = inr (cont (#read tape) , tape)
  step ($halt result , tape)       = inl result

  -- Returns the result of running a turing machine wrapped into the 'Delay' monad
  run : TM → Tape → Delay Result
  forceDelay (run tm tape) with step (tm , tape)
  … | inl result        = now result             -- computation finished, return the result
  … | inr (tm' , tape') = later (run tm' tape')  -- computation not finished, continue running
