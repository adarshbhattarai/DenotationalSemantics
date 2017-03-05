-----------------------------------------------------------------------------
--
-- Module      :  :  DSem_imp
-- APL Lab Template in Haskell!!
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
-- Imp: expressions language (Watt, Ex. 3.6)	--
--      with commands    (store).. 		--
--      and  definitions (evnironment).. 	--
--
--     (A nicer version of Ex. 4.7 from text)	--
-- --------------------------------------------	--
--
-----------------------------------------------------------------------------
module DSemImp
 ( impTests )
 where

-- --------------------------------------------	--
-- ---------- Abstract Syntax -----------------	--

			-- terminal nodes of the syntax --
type      Numeral  = Int
type      Ident    = String

			-- parsed phrases of the abstract syntax --
data Command =
              Skip
            | Assign   (Ident,       Expression)
            | Letin    (Declaration, Command   )
            | Cmdcmd   (Command,     Command   )
            | Ifthen   (Expression,  Command, Command)
            | Whiledo  (Expression,  Command   )
            | ForTo    (Numeral,Numeral,Numeral,Command)

data Expression =
            Num    Numeral
    	    | False_
    	    | True_
    	    | Notexp   Expression
    	    | Id       Ident
    	    | Sumof   (Expression,  Expression)
    	    | Subof   (Expression,  Expression)
    	    | Prodof  (Expression,  Expression)
    	    | Less    (Expression,  Expression)
    	    
          | Take    (Expression,  Expression)
          | Fst Expression
          | Snd Expression
         -- | Leten   (Declaration, Expression)
         --   deriving Show

data Declaration =
	      Constdef (Ident,  Expression)
	    | Vardef   (Ident,  TypeDef   )

data TypeDef =
	      Bool | Int | TypeDef TypeDef
	
-- --------------------------------------------	--
-- ---------- Semantic Domains ----------------	--

type	Integer	= Int
type	Boolean	= Bool
type	Location	= Int

data	Value	= IntValue    Int
		        | TruthValue  Bool
-- Pairvalue   PairValue
                  deriving (Eq, Show)

type	Storable  = Value

data	Bindable  = Const Value | Variable Location
                  deriving (Eq, Show)

data	Denotable = Unbound | Bound Bindable
                  deriving (Eq, Show)

data  PairValue = Value Value

-- --------------------------------------------	--
-- ---------- Semantic Functions --------------	--
valuation :: Int         -> Value
evaluate  :: Expression  -> Environ -> Store ->  Value
elaborate :: Declaration -> Environ -> Store ->  (Environ,Store)
execute   :: Command     -> Environ -> Store ->  Store

-- --------------------------------------------	--
-- ---------- Auxiliary Semantic Functions ----	--
add   (x, y) = x + y
diff  (x, y) = x - y
prod  (x, y) = x * y

lessthan  (x, y) = x < y


-- ---------- Storage   ---------- --
-- fun deallocate sto loc:Location = sto	-- ... later --

data Sval  = Stored Storable | Undef | Unused

-- The actual storage in a Store
type DataStore = Location -> Sval

--	                 --bot---   --top---  --data---
data Store = Store (Location,  Location,  DataStore)

update :: (Store, Location, Value) -> Store
update (Store(bot,top,sto), loc, v) =
	let new adr = if adr==loc
			      then Stored v else (sto adr)
	in Store( bot, top, new)

		-- fetch from store, and convert into Storable (=Const)
fetch ::(Store,Location) -> Storable
fetch  (Store(bot,top,sto), loc)  =
	let stored_value(Stored stble) = stble
	    stored_value(Unused)       = error ("Store: Unused")
	    stored_value(Undef)        = error ("Store: Undefined ")
	in  stored_value(sto loc)

		-- create a new "undefined" location in a store
allocate :: Store -> (Store, Location)
allocate ( Store(bot,top,sto) )  =
	let newtop  = top+1
	    new adr = if adr==newtop
			      then Undef else (sto adr)
	in (Store( bot, newtop, new), newtop)

-- ---------- Envirionment   ----------
type  Environ  =  Ident -> Denotable

bind :: (Ident,Bindable) -> Environ
bind  (name, val) =  \id -> if id==name
                            then Bound(val) else Unbound

-- look through the layered environment bindings
find :: (Environ, Ident) -> Bindable
find  (env, id)  =
	let getbv(Bound bdbl) = bdbl
	    getbv(Unbound)    = error ("undefined: " ++ id)
	in getbv( env id)

overlay :: (Environ, Environ) -> Environ
overlay  (env', env)  =
	\id -> let val = env' id
	       in  if val/=Unbound then val
	                            else env id

-- ---------- Etc...
--    coerce a Bindable into a Const..
coerc :: (Store, Bindable) -> Value
coerc (sto, Const v)      = v
coerc (sto, Variable loc) = fetch(sto,loc)

-- ---------- Initialize system  ----------
env_null :: Environ
env_null =  \i -> Unbound

--store_null =  empty --(=0) --, addressing starts at 1
sto_init :: DataStore
sto_init =  \loc -> Unused

sto_null :: Store
sto_null =  Store( 1, 0, sto_init)

-- --------------------------------------------
-- ---------- Semantic Equations --------------

				-- from integer to Const Value
valuation ( n ) = IntValue(n)

execute ( Skip ) env sto = sto

execute ( Assign(name,exp) ) env sto  =
     		let rhs = evaluate exp env sto
     		    Variable loc = find( env,name)
     		in  update( sto, loc, rhs)

execute ( Letin(def,c) ) env sto =
     		let (env', sto') = elaborate def env sto
            in execute c (overlay(env',env)) sto'

execute ( Cmdcmd(c1,c2) ) env sto  =
     		let sto' = execute c1 env sto
            in execute c2 env sto'

execute ( Ifthen(e,c1,c2) ) env sto =
     		if evaluate e env sto == TruthValue True
            then execute c1 env sto
            else execute c2 env sto

execute ( Whiledo(e,c) ) en st =
     		let executeWhile en st =  if evaluate e en st == TruthValue True
                                        then executeWhile en (execute c en st)
                                        else st
            in
            executeWhile en st

----------------Adding New feature-------------

  -------From e1 to e2 in steps of e3 execute c
execute (ForTo(e1,e2,e3,c)) env sto = 
                let forLoop e1 env sto = if( e1 + e3 < e2 )
                                         then forLoop (e1+e3) env ( execute c env sto) 
                                         else sto
                in
                    forLoop e1 env sto

------------------------------------------------
     			-- simple, just build a Const
evaluate ( Num(n)  )  env sto  = IntValue n
evaluate ( True_   )  env sto  = TruthValue  True
evaluate ( False_  )  env sto  = TruthValue  False

     			-- lookup id, and  coerce as needed
evaluate ( Id(n)  )  env sto  = coerc( sto, find(env,n) )

     			-- get Consts, and compute result
evaluate ( Sumof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
     	    IntValue i2 = evaluate e2 env sto
     	in  IntValue  ( add(i1,i2) )

evaluate ( Subof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in  IntValue ( diff(i1,i2) )

evaluate ( Prodof(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in  IntValue ( prod(i1,i2) )


evaluate ( Less(e1,e2) ) env sto =
     	let IntValue i1 = evaluate e1 env sto
            IntValue i2 = evaluate e2 env sto
        in  TruthValue ( lessthan(i1,i2) )

evaluate ( Notexp(e) ) env sto =
     	if evaluate e env sto == TruthValue True
            then TruthValue False 
            else TruthValue True

{-- --------- * There was error
evaluate (Take (e1, e2)) env sto =
          let v1 = evaluate e1 env sto
              v2 = evaluate e2 env sto 
          in Pairvalue v1 v2 

evaluate (Fst (e1)) env sto =
        let Pairvalue val1 val2 = evaluate e1 env sto 
        in val1


evaluate (Snd (e1)) env sto =
        let Pairvalue (val1, val2) = evaluate e1 env sto 
        in val2
--}

{-- ------- * Later...
     			-- layer environment, and compute result
evaluate ( leten(def,e) ) env sto =
     	let (env', sto') = elaborate def env sto
		in  evaluate e (overlay (env', env)) sto'
   ------- --}

elaborate ( Constdef(name,e) ) env sto =
     	let v = evaluate e env sto
		in  ( bind(name, Const  v), sto )

elaborate ( Vardef(name,tdef) ) env sto =
     	let (sto',loc) = allocate sto
		in  ( bind(name, Variable loc), sto' )

-- ============================================	 --

-- ============================== --
-- ========== Test it! ========== --
-- print "----------  Test";
e1 = Num(2)

e2 = Sumof(Num(1),Num(2))

st = update (sto_null, 1, IntValue 1)

v  = IntValue 5

en = bind("i",Const v )  


v1 = evaluate e1 en st      -- = 2

v2 = evaluate e2 en st      -- = 3




v3 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3)))) en st             -- = 7


v4 = evaluate (Sumof(Num(1), Prodof(Num(2),Num(3)))) env_null sto_null -- = 7


v6 = evaluate (Notexp (True_) ) en st                           -- False


v7 = evaluate (Less( Num (1) , Subof( Num(3), Num (1)))) en st  -- True



dx  = Constdef("x",Num(2))  -- a declaration

dxx = elaborate dx env_null sto_null


pgm =

  Letin( Constdef( "x", Num(2)),

         Letin( Vardef( "y", Int),

            Cmdcmd( Assign( "y", Num(3)),

                Ifthen( Less(Id("x"),Id("y")),

                    Assign("y",Num(1)),

                    Assign("y",Num(2))

                )

            )

        )

         )

  

s1 = execute pgm  env_null sto_null    -- y = 1


x_ = Id("x")    -- a shorthand...

y_ = Id("y")

z_ = Id("z")


pgm3 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

                  Letin ( Vardef( "z", Int),

                      Cmdcmd( Assign( "z",Num(0)),

                                      Assign("z", Sumof(z_,Num(1)))

                      )

                  )

              )

          )

       )


sto3 = execute pgm3  env_null sto_null   -- y = 3, z = 1



v5 = map (curry fetch sto3) [ 1, 2 ]


  -- dump the store....

dump :: Store -> [Value]
dump (sto @ (Store(lo, hi, dat)) ) =

    map (curry fetch sto) [lo .. hi]


s2 = dump sto3




x = Id("x") -- a shorthand...

y = Id("y")

z = Id("z")

pgm2 =

  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

                  Letin ( Vardef( "z", Int),

                      Cmdcmd( Assign( "z",Num(0)),

                                      Whiledo( Less(Num(0),y_),

                                          Cmdcmd( Assign("z", Sumof(z_,x_)),

                                                  Assign("y", Subof(y_,Num(1)))

                          )

                      )

                      )

                  )

              )

          )

       )

  

sto2 = execute pgm2  env_null sto_null   -- y= 0 , z = 2 + 2 + 2 = 6



    -- dump the store....

    -- y  z 

s3 = dump sto2

-- ------------------------------------------
-- ----------Manual Test---------------------

pgm4 =
  Letin( Constdef( "x", Num(2)),

       Letin( Vardef( "y", Int),

              Cmdcmd( Assign( "y", Num(3)),

                  Letin ( Vardef( "z", Int),

                      Cmdcmd( Assign( "z",Num(0)),

                                      ForTo( 0, 10 , 2 ,

                                          Cmdcmd( Assign("z", Sumof(z_,x_)),

                                                  Assign("y", Prodof(y_,Num(2)))

                          )))))))

       

sto5 = execute pgm4  env_null sto_null
s4   = dump sto5

factorial :: (Eq a, Num a) => a -> a
factorial n = if n == 0 then 1 else n * factorial ( n - 1)

power :: (Num a, Integral b) => a -> b -> a
power x 1  = x
power x n  = x * power x (n-1)

--------------------------------------------
impTestStos = [ dump s1, s2, s3 ]
impTestVals = [ v1, v2, v3 ]
manTestVals = [ v4, v6, v7 ]
manTestStos = [ s4]
fact        = [ factorial 5]
pow         = [ power 5 3]

--c1 = Equal(e1)
--c2 = Equal(e2)
--v4 = execute c1 s1
--v5 = execute c2 s1

impTests =  do print "------APL:: DSem_imp"
               print impTestVals
               print impTestStos
               print "-------Manual Test---"
               print manTestStos
               print manTestVals
               print "-------Factorial  ---"
               print fact
               print "-------Power      ---"
               print pow