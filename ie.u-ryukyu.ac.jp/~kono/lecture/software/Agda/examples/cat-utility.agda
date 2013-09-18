module cat-utility where

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

        open import Category -- https://github.com/konn/category-agda
        open import Level
        --open import Category.HomReasoning
        open import HomReasoning

        open Functor

        id1 :   ∀{c₁ c₂ ℓ  : Level} (A : Category c₁ c₂ ℓ)  (a  : Obj A ) →  Hom A a a
        id1 A a =  (Id {_} {_} {_} {A} a)
        -- We cannot make A implicit

        record IsUniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') 
                         ( U : Functor B A )
                         ( F : Obj A → Obj B )
                         ( η : (a : Obj A) → Hom A a ( FObj U (F a) ) )
                         ( _* : { a : Obj A}{ b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b )
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
           field
               universalMapping :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } → 
                             A [ A [ FMap U ( f * ) o  η a ]  ≈ f ]
               uniquness :   {a : Obj A} { b : Obj B } → { f : Hom A a (FObj U b) } → { g :  Hom B (F a) b } → 
                             A [ A [ FMap U g o  η a ]  ≈ f ] → B [ f * ≈ g ]

        record UniversalMapping  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') 
                         ( U : Functor B A )
                         ( F : Obj A → Obj B )
                         ( η : (a : Obj A) → Hom A a ( FObj U (F a) ) )
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
            infixr 11 _*
            field
               _* :  { a : Obj A}{ b : Obj B} → ( Hom A a (FObj U b) ) →  Hom B (F a ) b 
               isUniversalMapping : IsUniversalMapping A B U F η _*

        open NTrans
        open import Category.Cat
        record IsAdjunction  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') 
                         ( U : Functor B A )
                         ( F : Functor A B )
                         ( η : NTrans A A identityFunctor ( U ○  F ) )
                         ( ε : NTrans B B  ( F ○  U ) identityFunctor )
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
           field
               adjoint1 :   { b : Obj B } →
                             A [ A [ ( FMap U ( TMap ε b ))  o ( TMap η ( FObj U b )) ]  ≈ id1 A (FObj U b) ]
               adjoint2 :   {a : Obj A} →
                             B [ B [ ( TMap ε ( FObj F a ))  o ( FMap F ( TMap η a )) ]  ≈ id1 B (FObj F a) ]

        record Adjunction {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') 
                         ( U : Functor B A )
                         ( F : Functor A B )
                         ( η : NTrans A A identityFunctor ( U ○  F ) )
                         ( ε : NTrans B B  ( F ○  U ) identityFunctor )
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
            field
               isAdjunction : IsAdjunction A B U F η ε
            U-functor =  U
            F-functor =  F
            Eta = η
            Epsiron = ε


        record IsMonad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) 
                         ( T : Functor A A )
                         ( η : NTrans A A identityFunctor T )
                         ( μ : NTrans A A (T ○ T) T)
                         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
           field
              assoc  : {a : Obj A} → A [ A [ TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
              unity1 : {a : Obj A} → A [ A [ TMap μ a o TMap η ( FObj T a ) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
              unity2 : {a : Obj A} → A [ A [ TMap μ a o (FMap T (TMap η a ))] ≈ Id {_} {_} {_} {A} (FObj T a) ]

        record Monad {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) (T : Functor A A) (η : NTrans A A identityFunctor T) (μ : NTrans A A (T ○ T) T)
               : Set (suc (c₁ ⊔ c₂ ⊔ ℓ )) where
          field
            isMonad : IsMonad A T η μ
             -- g ○ f = μ(c) T(g) f
          join : { a b : Obj A } → { c : Obj A } →
                              ( Hom A b ( FObj T c )) → (  Hom A a ( FObj T b)) → Hom A a ( FObj T c )
          join {_} {_} {c} g f = A [ TMap μ c  o A [ FMap T g o f ] ]


        Functor*Nat :  {c₁ c₂ ℓ c₁' c₂' ℓ' c₁'' c₂'' ℓ'' : Level} (A : Category c₁ c₂ ℓ) {B : Category c₁' c₂' ℓ'} (C : Category c₁'' c₂'' ℓ'')
            (F : Functor B C) -> { G H : Functor A B } -> ( n : NTrans A B G H ) -> NTrans A C (F ○  G) (F ○ H)
        Functor*Nat A {B} C F {G} {H} n = record {
               TMap  = \a -> FMap F (TMap n a)
               ; isNTrans = record {
                    commute = commute
               }
            } where
                 commute : {a b : Obj A} {f : Hom A a b} 
                    → C [ C [ (FMap F ( FMap H f )) o  ( FMap F (TMap n a)) ]  ≈ C [ (FMap F (TMap n b )) o  (FMap F (FMap G f))  ] ]
                 commute  {a} {b} {f}  = let open ≈-Reasoning (C) in
                    begin  
                       (FMap F ( FMap H f )) o  ( FMap F (TMap n a))
                    ≈⟨ sym (distr F) ⟩
                       FMap F ( B [ (FMap H f)  o TMap n a ])
                    ≈⟨ IsFunctor.≈-cong (isFunctor F) ( nat n ) ⟩
                       FMap F ( B [ (TMap n b ) o FMap G f ] )
                    ≈⟨ distr F ⟩
                       (FMap F (TMap n b )) o  (FMap F (FMap G f))
                    ∎

        Nat*Functor :  {c₁ c₂ ℓ c₁' c₂' ℓ' c₁'' c₂'' ℓ'' : Level} (A : Category c₁ c₂ ℓ) {B : Category c₁' c₂' ℓ'} (C : Category c₁'' c₂'' ℓ'')
            { G H : Functor B C } -> ( n : NTrans B C G H ) -> (F : Functor A B) -> NTrans A C (G ○  F) (H ○ F)
        Nat*Functor A {B} C {G} {H} n F = record {
               TMap  = \a -> TMap n (FObj F a)
               ; isNTrans = record {
                    commute = commute
               }
            } where
                 commute : {a b : Obj A} {f : Hom A a b} 
                    → C [ C [ ( FMap H (FMap F f )) o  ( TMap n (FObj F a)) ]  ≈ C [ (TMap n (FObj F b )) o  (FMap G (FMap F f))  ] ]
                 commute  {a} {b} {f}  =  IsNTrans.commute ( isNTrans n) 

        -- T ≃  (U_R ○ F_R)
        -- μ = U_R ε F_R
        --      nat-ε
        --      nat-η     -- same as η but has different types

        record MResolution {c₁ c₂ ℓ  c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) ( B : Category c₁' c₂' ℓ' ) 
              ( T : Functor A A ) 
              -- { η : NTrans A A identityFunctor T }
              -- { μ : NTrans A A (T ○ T) T }
              -- { M : Monad A T  η μ }
              ( UR : Functor B A ) ( FR : Functor A B )
              { ηR : NTrans A A identityFunctor  ( UR ○ FR ) } 
              { εR : NTrans B B ( FR ○ UR ) identityFunctor } 
              { μR : NTrans A A ( (UR ○ FR)  ○ ( UR ○ FR )) ( UR ○ FR  ) }
              ( Adj : Adjunction A B UR FR ηR εR  )
                        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁' ⊔ c₂' ⊔ ℓ' )) where
                   field
                      T=UF  :  T ≃  (UR ○ FR) 
                      μ=UεF : {x : Obj A } -> A [ TMap μR x ≈ FMap UR ( TMap εR ( FObj FR x ) ) ]
                      -- ηR=η  : {x : Obj A } -> A [ TMap ηR x  ≈  TMap η x ] -- We need T -> UR FR conversion
                      -- μR=μ  : {x : Obj A } -> A [ TMap μR x  ≈  TMap μ x ]


