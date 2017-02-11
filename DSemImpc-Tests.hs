-----------------------------------------------------------------------------
--
-- Module      :  :  Imp'c_tests
-- APL:: IMPc DSem - Lab Tests
--
-- ----------------------------------------------	--
-- denotational semantics definitions: in Haskell	--
-- ----------------------------------------------	--
--
-----------------------------------------------------------------------------
module ImpcTest (

impTests        -- export the test results...

) where

-- --------------------------------------------	--
-- ============================================ --
-- ---------- Test it..! ---------------------- --

                          ---- some convienences..
kont_null :: Econt
kont_null v  = Output(v,Halt)

                          -- maybe this should dump the store?
cont_null :: Ccont
cont_null  = \any_store -> Halt

qont_null :: Dcont
qont_null  = \any_env -> cont_null

input, result :: Expression
input  = Id "input"       -- a shorthand..
result = Id "result"

                          -- dump the store....
dump :: Store -> [Value]
dump (sto @ (Store(lo, hi, datas) ) ) =
      map (curry fetch sto) [lo .. hi]

outVal :: Value -> String
outVal (IntValue   i) = "Integer" ++ show i
outVal (TruthValue b) = "boolean" ++ show b

outVals :: [Value] -> [String]
outVals xs = map outVal xs ++ ["\n"]

prints :: [Value] -> IO()
prints vs = print (outVals vs)

{- -- if you want the values on separate lines, then:
outVals = map outVal
prints  = putStr . unlines . outVals
-}

-- a continuation to dump the store....
dump_cont sto = do prints (dump sto)
                   return Halt

-- a continuation to output the store....
output_cont :: Store -> Answer
output_cont (sto @ (Store(lo, hi, dat)) ) =
    let put []     = Halt
        put (v:vs) = Output(v, put vs)
    in  put (dump sto)

{- ========== --
-- a continuation to output the store....
-- output_cont sto = reduce ( output oo pair ) Halt (dump sto)
output_cont :: Store -> Answer
output_cont sto = foldl (curry Output) Halt (dump sto)
 --}

-- =============================================== --
e1 = Num 2
e2 = Sumof (Num 1) (Num 2)

-- Trace_flag = "Test: expressions    [ 2, 1+2]"
a1 = evaluate e1 env_null kont_null sto_null;        --  = 2
a2 = evaluate e2 env_null kont_null sto_null;        --  = 3

-- Trace_flag = "Test: expressions    [ 1+2*3 = 7 ]"
a3 = evaluate (Sumof (Num 1) (Prodof (Num 2) (Num 3)))
                        env_null kont_null sto_null; --  = 7

test1() = do print ":---: expressions  [ 2, 1+2, 1+2*3 ]"
             print a1
             print a2
             print a3
-- ------------------------- --
dx = Constdef "x" (Num 2)      -- a declaration --
a4 = elaborate dx env_null qont_null sto_null

{- ========== --
a5 = evaluate (  Leten  dx (Sumof (Num 1) (Id "x") ) )
                        env_null kont_null sto_null; -- = 3
-- ========== --}
test2() = do print ":---: declaration    {const x = 2}"
             print a4
-- =============================================== --
--   result := input
pgm1 = Prog( Assign "result" input )

                        -- run the program on an input --
test3() = do print ":---: {result = input}  [1, 2]"
             print (run pgm1  1)
             print (run pgm1  2)
-- =============================================== --
--   result := input + 1
--
pgm2 = Prog( Assign "result" (Sumof (Num 1) input ) )

                        -- run the program on inputs --
test4() = do print ":---: {result = input+1}  [2, 3]"
             print $ run pgm2  1
             print $ run pgm2  2

{- -----------------------------------------------
 *   let value x ~ 2
 *   in let var y : int
 *      in  y:= 3
 *          if x<y then y:=1
 *                 else y:=2
 --}

-- Note that we do no output, so need to dump store for results
cmd' =
  Letin  (Constdef "x" (Num 2))
         (Letin (Vardef "y" Int)
                (Cmdcmd (Assign "y" (Num 3))
                        (Ifthen (Less (Id "x") (Id "y"))
                                (Assign "y" (Num 1))
                                (Assign "y" (Num 2))
                                )
                        )
                )

cmd =
  Letin (Constdef "x" (Num 2))
        (Letin (Vardef "y" Int)
               (Cmdcmd (Assign "y" (Num 3))
                       (Assign "y" (Num 1))
                       )
                )

                -- get Answer --
a9  = execute cmd  env_null   cont_null    sto_null

                -- get a full set Answers..!  --
a9b  = execute cmd  env_null  output_cont   sto_null

test5() = do print ":---: Simple Program.2  -> [1]"
             -- trace("Pre-a9") print "Pre-a9"
             print a9
             print a9b
             print $ run (Prog cmd) 000

{- --------------------------------------------------------
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z := 0
 *             z := z+1
 --}
x    = Id "x"      -- some shorthands...
y    = Id "y"
z    = Id "z"
zero = Num 0
one  = Num 1

cmd3 =
  Letin (Constdef "x" (Num 2))
        (Letin (Vardef "y" Int)
               (Cmdcmd (Assign "y" (Num 3))
                       (Letin (Vardef "z" Int)
                              (Cmdcmd (Assign "z" zero)
                                      (Assign "z" (Sumof z one))                                      )
                       )
                )
         )

a10a = execute cmd3  env_null   cont_null  sto_null
a10b = execute cmd3  env_null output_cont  sto_null

test6() = do print ":---: Simple Program.3  -> [3,1]"
             -- print (run (Prog cmd3) 0)
             print a10b

{- --------------------------------------------------------
 *   // a loop
 *   let Const  x ~ 2
 *   in let var y : int
 *      in y := 3
 *         let var z : int
 *         in  z:= 0            { multiply z = x*y }
 *             while 0<y do  z := z+x; y := y-1
 --}
cmd4 =
  Letin (Constdef "x" (Num 2))
        (Letin  (Vardef "y" Int)
                (Cmdcmd (Assign "y" (Num 3))
                        (Letin (Vardef "z" Int)
                               (Cmdcmd (Assign "z" zero)
                                       (Whiledo (Less zero y)
                                         (Cmdcmd (Assign "z" (Sumof z x  ))
                                                 (Assign "y" (Subof y one))
                                                  )
                                        )
                                )
                         )
                 )
         )

a11a = execute cmd4  env_null   cont_null  sto_null
a11b = execute cmd4  env_null output_cont  sto_null

test7() = do print ":---: Simple Program.4  -> [0,6, Halt]"
             -- print $ run (Prog cmd4) 0
             print a11b
-- --------------------------------------------------------
-- ==== Tests::

-- impcAns = [ a1, a2, a3a, a4, a5, a6, a7, a8 ]
-- impcAns = [ a1, a2, a3, a4, a6, a7]

impcTests = do print "------ APL:: DSem_impc"
               test1()   -- Expressions
               test2()   -- Declarations
               test3()   -- Expressions
               test4()   -- Expressions
               test5()   -- simple program.2
               test6()   -- simple program.3
               test7()   -- simple program.4
               putStrLn $ draw e2

-- ============================================	 --
