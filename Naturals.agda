module Naturals where

open import Library
open import Categories
open import Functors

open Fun

record NatT {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}(F G : Fun C D) : Set (a ⊔ b ⊔ d) where
  constructor natural
  open Cat
  field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
        nat : ∀{X Y}{f : Hom C X Y} → 
              _∙_ D (HMap G f) cmp ≅ _∙_ D cmp (HMap F f)

-- Dos transformaciones naturales son iguales si sus componentes son iguales.
NatTEq : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G : Fun C D}
         {α β : NatT F G} → 
         (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X}) → 
         α ≅ β
NatTEq {α = natural cmp _} {natural .cmp _} refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

-- NatTEq2 se puede usar cuando los funtores intervinientes no son definicionalmente iguales
NatTEq2 : ∀ {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G F' G' : Fun C D}
            {α : NatT F G}{β : NatT F' G'}
          → F ≅ F' → G ≅ G'  
          → (λ {X} → NatT.cmp α {X}) ≅ (λ {X} → NatT.cmp β {X})
          → α ≅ β
NatTEq2 {α = natural cmp _} {natural .cmp _} refl refl refl =
  cong (natural cmp) (iext λ _ → iext λ _ → iext λ _ → ir _ _)

--------------------------------------------------
-- la identidad es una transformación natural
idNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F : Fun C D} → NatT F F
idNat {D = D}{F} = let open Cat D in natural iden (λ {X}{Y}{f} -> 
                   proof
                   HMap F f ∙ iden
                   ≅⟨ idr ⟩
                   HMap F f
                   ≅⟨ sym idl ⟩
                   iden ∙ HMap F f
                   ∎)

-- Composición (vertical) de transformaciones naturales
compVNat : ∀{a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compVNat {D = D}{F}{G}{H} b a = let open Cat D; open NatT in
                                natural ((cmp b) ∙ (cmp a))
                                        (λ {X}{Y}{f} -> 
                proof
                HMap H f ∙ (cmp b ∙ cmp a)
                ≅⟨ sym ass ⟩
                (HMap H f ∙ cmp b) ∙ cmp a
                ≅⟨ cong (λ x -> x ∙ cmp a) (nat b) ⟩
                (cmp b ∙ HMap G f) ∙ cmp a
                ≅⟨ ass ⟩
                cmp b ∙ (HMap G f ∙ cmp a)
                ≅⟨ cong ((_∙_) (cmp b)) (nat a) ⟩
                cmp b ∙ (cmp a ∙ HMap F f)
                ≅⟨ sym ass ⟩
                (cmp b ∙ cmp a) ∙ HMap F f
                ∎ )

--------------------------------------------------
{- Categorías de funtores
 Dadas dos categorías C y D, los objetos son los funtores : C → D,
 y los morfismos son las transformaciones naturales entre ellos.
-}

FunctorCat : ∀{a b c d} → Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = record{
  Obj  = Fun C D;
  Hom  = NatT;
  iden = idNat;
  _∙_  = compVNat;
  idl  = NatTEq (iext (λ _ → idl));
  idr  = NatTEq (iext (λ _ → idr));
  ass  = NatTEq (iext (λ _ → ass))}
  where open Cat D
--------------------------------------------------
-- Algunos ejemplos de transformaciones naturales

module Ejemplos where

 open import Categories.Sets
 open import Functors.List
 open import Functors.Maybe
 open import Functors.Constant
 open import Data.Nat

 {- reverse es una transformación natural -}

 open Cat (Sets {lzero})

 concatmap-distr : {X Y : Set}{f : X -> Y}(xs ys : List X) ->
           mapList f (xs ++ ys) ≅ mapList f xs ++ mapList f ys
 concatmap-distr [] ys = refl
 concatmap-distr (x ∷ xs) ys = cong₂ _∷_ refl (concatmap-distr xs ys)

{- reverse-distr : {X : Set}(x : X)(xs : List X) ->
                 reverse (x ∷ xs) ≅ reverse xs ++ (x ∷ [])
 reverse-distr x [] = refl
 reverse-distr x (y ∷ xs) = proof
                             reverse (x ∷ y ∷ xs)
                             ≅⟨ {!!} ⟩
                             reverse xs ++ (y ∷ [] ++ x ∷ [])
                             ≅⟨ {!!} ⟩
                             (reverse xs ++ y ∷ []) ++ x ∷ []
                             ≅⟨ cong₂ _++_ (sym (reverse-distr y xs)) refl ⟩
                             reverse (y ∷ xs) ++ x ∷ []
                             ∎
-}

--
-- map f (foldl c n xs) = foldl c (map f n) (map f xs) pattern matching en xs
-- c = λ r -> x : r
--
-- revNat-aux2 : {X Y : Set} {f : X -> Y}(x : X)(y : Y)(xs : List X) ->   mapList f (foldl (λ r -> x ∷ r) y xs) ≅ foldl (λ r -> x ∷ r) (mapList f n) (mapList f xs)
-- revNat-aux2 = {!!}
 
 revNat-aux : {X Y : Set} {f : X -> Y}(x : X)(xs : List X) -> reverse (x ∷ xs) ≅ reverse xs ++ x ∷ []
 revNat-aux x [] = refl
 revNat-aux x (y ∷ xs) = {!!}

 revNat-proof : {X Y : Set} {f : X -> Y}(a : List X) →
      mapList f (reverse a) ≅ reverse (mapList f a)
 revNat-proof [] = refl
 revNat-proof {f = f} (x ∷ xs) = proof
                      mapList f (reverse (x ∷ xs))
                      ≅⟨ {!!} ⟩
                      mapList f ((reverse xs) ++ (x ∷ []))
                      ≅⟨ concatmap-distr (reverse xs) (x ∷ []) ⟩
                      (mapList f (reverse xs)) ++ mapList f (x ∷ [])
                      ≅⟨ cong₂ _++_ (revNat-proof xs) refl ⟩
                      reverse (mapList f xs) ++ (f x ∷ [])
                      ≅⟨ {!!} ⟩
                      reverse ((f x) ∷ mapList f xs)
                      ∎

 revNat : NatT ListF ListF
 revNat = natural reverse (ext revNat-proof)

 --

 concatNat-proof :  {X Y : Set} {f : X -> Y} (a : List (List X)) →
      (mapList f) (concat a) ≅ concat (mapList (mapList f) a)
 concatNat-proof [] = refl
 concatNat-proof {f = f} (x ∷ xs) = proof
                        mapList f (concat (x ∷ xs)) 
                        ≅⟨ cong (mapList f) refl ⟩
                        mapList f (x ++ concat xs)
                        ≅⟨ concatmap-distr x (concat xs) ⟩
                        (mapList f x) ++ mapList f (concat xs)
                        ≅⟨ cong ((_++_) (mapList f x)) (concatNat-proof xs) ⟩
                        (mapList f x) ++ concat (mapList (mapList f) xs)
                        ≅⟨ refl ⟩
                        concat (mapList f x ∷ mapList (mapList f) xs)
                        ∎

 concatNat : NatT (ListF ○ ListF) ListF
 concatNat = natural concat (ext concatNat-proof)

 --
 lengthNat-proof : {X Y : Set} {f : X → Y} (a : List X) →
       length a ≅ length (HMap ListF f a)
 lengthNat-proof [] = refl
 lengthNat-proof {f = f}(x ∷ as) = cong suc (lengthNat-proof as)

 lengthNat : NatT ListF (K ℕ)
 lengthNat = natural length (ext lengthNat-proof)

 --
 safeHead : {A : Set} → List A → Maybe A
 safeHead [] = nothing
 safeHead (x ∷ xs) = just x

 headNat-proof : {X Y : Obj} {f : Hom X Y}(xs : List X) →
      (HMap MaybeF f ∙ safeHead) xs ≅ (safeHead ∙ HMap ListF f) xs
 headNat-proof [] = refl
 headNat-proof (x ∷ xs) = refl

 headNat : NatT ListF MaybeF
 headNat = natural safeHead (ext headNat-proof)

 --
--------------------------------------------------
-- Natural isomorphism
{- Un isomorfismo natural es una transformación natural tal que
   cada componente es un isomorfismo. -}
open import Categories.Iso

record NatIso {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
             {F G : Fun C D}(η : NatT F G)  : Set (a ⊔ d) where
  constructor natiso
  field cmpIso : ∀{X} -> Iso D (NatT.cmp η {X})


--------------------------------------------------
-- composición con funtor (a izquierda y a derecha)
compFNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}
         → (J : Fun D E)
         → (η : NatT F G) → NatT (J ○ F) (J ○ G)
compFNat {D = D} {E} {F} {G} J n =
               let open NatT n
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in
               natural (HMap J cmp) (λ {X}{Y}{f} -> proof
                    (HMap J (HMap G f)) ∙E HMap J cmp 
                    ≅⟨ sym (fcomp J) ⟩
                    HMap J ((HMap G f) ∙D cmp)
                    ≅⟨ cong (HMap J) nat ⟩
                    HMap J (cmp ∙D (HMap F f))
                    ≅⟨ fcomp J ⟩
                    HMap J cmp ∙E (HMap J (HMap F f))
                    ∎ )

compNatF :  ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {J K : Fun D E}
         → (η : NatT J K)
         → (F : Fun C D)
         → NatT (J ○ F) (K ○ F)
compNatF {C = C} {D} {E} {J} {K} n F =
               let open NatT n
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in natural cmp nat

--------------------------------------------------
-- Composición horizontal
compHNat : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
            {F G : Fun C D}{J K : Fun D E}
            (η : NatT F G)(ε : NatT J K)
            → NatT (J ○ F) (K ○ G)
compHNat {D = D}{E}{F}{G}{J}{K} n e = let open NatT
                                          open Cat E renaming (_∙_ to _∙E_ ; ass to assE)
                                          open Cat D renaming (_∙_ to _∙D_ ; ass to assD)
                        in natural (λ {X} → HMap K (cmp n) ∙E cmp e)
                        (λ {X}{Y}{f} -> proof
                        HMap K (HMap G f) ∙E HMap K (cmp n) ∙E cmp e
                        ≅⟨ sym assE ⟩
                        (HMap K (HMap G f) ∙E HMap K (cmp n)) ∙E cmp e
                        ≅⟨ sym (cong (λ x -> x ∙E cmp e) (fcomp K)) ⟩
                        HMap K (HMap G f ∙D cmp n) ∙E cmp e
                        ≅⟨ cong (λ x -> HMap K x ∙E cmp e) (nat n) ⟩
                        HMap K (cmp n ∙D HMap F f) ∙E cmp e
                        ≅⟨ cong ((λ x -> x ∙E cmp e)) (fcomp K) ⟩
                        (HMap K (cmp n) ∙E HMap K (HMap F f)) ∙E cmp e
                        ≅⟨ assE ⟩
                        HMap K (cmp n) ∙E HMap K (HMap F f) ∙E cmp e
                        ≅⟨ cong ((_∙E_) (HMap K (cmp n))) (nat e) ⟩
                        HMap K (cmp n) ∙E cmp e ∙E HMap J (HMap F f)
                        ≅⟨ sym assE ⟩
                        (HMap K (cmp n) ∙E cmp e) ∙E HMap J (HMap F f)
                        ∎)



-- La composición horizontal es asociativa
compHNat-assoc : ∀{a1 b1 a2 b2 a3 b3 a4 b4}
                    {C1 : Cat {a1} {b1}}{C2 : Cat {a2} {b2}}{C3 : Cat {a3} {b3}}{C4 : Cat {a4} {b4}}
                    {F G : Fun C1 C2}{J K : Fun C2 C3}{L M : Fun C3 C4} 
                 →  (η1 : NatT F G)(η2 : NatT J K)(η3 : NatT L M)
                 →  compHNat (compHNat η1 η2) η3 ≅ compHNat η1 (compHNat η2 η3)
compHNat-assoc {C3 = C3}{C4 = C4}{J = J}{K}{L}{M} (natural cmp1 _) (natural cmp2 _) (natural cmp3 _) =
                   let   _∙4_ = Cat._∙_ C4
                         _∙3_ = Cat._∙_ C3
                         ass4 = Cat.ass C4
                   in
                     NatTEq2 (Functor-Eq refl refl) (Functor-Eq refl refl)
                     (iext (λ X → proof
                     (HMap M ((HMap K cmp1) ∙3 cmp2)) ∙4 cmp3
                     ≅⟨ cong (λ x -> x ∙4 cmp3) (fcomp M) ⟩
                     (HMap M (HMap K cmp1) ∙4 (HMap M cmp2)) ∙4 cmp3
                     ≅⟨ ass4 ⟩
                     (HMap M (HMap K cmp1)) ∙4 ((HMap M cmp2) ∙4 cmp3)
                     ∎))


-- ley de intercambio
interchange : ∀{a b c d e f}{C : Cat {a} {b}}{D : Cat {c} {d}}{E : Cat {e} {f}}
               {F G H : Fun C D}{I J K : Fun D E}
              → (α : NatT F G) → (β : NatT G H)
              → (γ : NatT I J) → (δ : NatT J K)
              → compHNat (compVNat β α) (compVNat δ γ) ≅ compVNat (compHNat β δ) (compHNat α γ)
interchange {D = D}{E}{I = I}{J}{K} (natural a _) (natural b _) (natural y _) (natural d natd) =
          let open NatT
              _∙D_ = Cat._∙_ D
              open Cat E
           in
           NatTEq (iext (λ X → proof
           HMap K (b ∙D a) ∙ d ∙ y
           ≅⟨ cong (λ x -> x ∙ d ∙ y) (fcomp K) ⟩
           (HMap K b ∙ HMap K a) ∙ d ∙ y
           ≅⟨ sym ass ⟩
           ((HMap K b ∙ HMap K a) ∙ d) ∙ y
           ≅⟨ cong (λ x -> x ∙ y) ass ⟩
           (HMap K b ∙ (HMap K a ∙ d)) ∙ y
           ≅⟨ cong (λ x -> (HMap K b ∙ x) ∙ y) natd ⟩
           (HMap K b ∙ (d ∙ HMap J a)) ∙ y
           ≅⟨ cong ((λ x -> x ∙ y)) (sym ass) ⟩
           ((HMap K b ∙ d) ∙ HMap J a) ∙ y
           ≅⟨ ass ⟩
           (HMap K b ∙ d) ∙ HMap J a ∙ y
           ∎))


