   procedure ArgList_Not_Full (L : ArgList; N : AFSize) is
      NewL : ArgList := L;
      NewL2 : ArgList;
      List : NatArray;
      NewN : AFSize := N;
      a : Arg;
   begin

      pragma Assert (L.Size <= N);
      if L.Size = N then
         for I in 0 .. N loop
            --pragma Assert (NewL.Size <= NewN);
            pragma Loop_Invariant (NewL.Size = N-I);
            pragma Loop_Invariant (NewN = N-I);
            pragma Loop_Invariant (for all I in 1 .. NewL.Size => NewL.List(I) <= NewN);
            pragma Loop_Invariant (Is_ArgList(NewL));
            pragma Loop_Invariant (Is_ArgList_For(NewL,NewN));
            pragma Loop_Invariant (for some a in 1 .. N-I => not ArgSet_From_ArgList(NewL,NewN)(a));
            List := NewL.List;
            if not ArgSet_From_ArgList(NewL,NewN)(N-I) or NewL.List(N-I) = N-I then
               pragma Assert (for all K in 1 .. NewL.Size-1 => NewL.List(K) <= NewN);
               a := NewL.List(N-I);
               pragma Assert (if not ArgSet_From_ArgList(NewL,NewN)(N-I) then a <= N-I-1);
               pragma Assert (if NewL.List(N-I) = N-I then (for some a in 1 .. N-I-1 => not ArgSet_From_ArgList(NewL,NewN)(a)));
               List(N-I) := 0;
               NewL := ArgList'(Size => N-I-1, List => List);
               NewN := N-I-1;
               --pragma Assert (for all K in 1 .. NewL.Size => not NewL.List(K) = );
               pragma Assert (not ArgSet_From_ArgList(NewL,NewN)(a));
               pragma Assert (for some a in 1 .. N-I-1 => not ArgSet_From_ArgList(NewL,NewN)(a));
            else
               List(N-I) := 0;
               for J in 1 .. N-I-1 loop
                  --pragma Loop_Invariant (for all K in 1 .. J-1 => (if NewL.List(K) = N-I then List(K) = NewL.List(N-I) and (for all M in 1 .. N-I-1 => (if M /= K then List(M) = NewL.List(M)))));
                  pragma Loop_Invariant (for all K in 1 .. J-1 => (if NewL.List(K) = N-I then List(K) = NewL.List(N-I) and (for some a in 1 .. N-I => not ArgSet_From_ArgList(NewL,NewN)(a))));
                  pragma Loop_Invariant (for all K in 1 .. J-1 => List(K) <= NewN-1);
                  pragma Loop_Invariant (for all K in J .. N-I-1 => List(K) = NewL.List(K));
                  pragma Loop_Invariant (for all K in 1 .. N-I-1 => (if NewL.List(K) /= N-I then List(K) = NewL.List(K) and List(K) /= NewL.List(N-I)));
                  pragma Loop_Invariant (for all K in 1 .. N-I-1 => (List(K) /= 0 and not (for some J in 1 .. N-I-1 => (J /= K and List(J) = List(K)))));
                  pragma Loop_Invariant (if (for all K in 1 .. N-I => NewL.List(K) /= J) then (for all K in 1 .. N-I-1 => List(K) /= J));
                  --pragma Loop_Invariant (if not ArgSet_From_ArgList(NewL,NewN)(J) then not ArgSet_From_ArgList(ArgList'(Size => N-I-1, List => List),N-I-1)(J));
                  if NewL.List(J) = N-I then
                     List(J) := NewL.List(N-I);
                  end if;
               end loop;
               pragma Assert (for all J in 1 .. N-I-1 => (if (for all K in 1 .. N-I => NewL.List(K) /= J) then (for all K in 1 .. N-I-1 => List(K) /= J)));
               pragma Assert (for some J in 1 .. N-I-1 => not ArgSet_From_ArgList(NewL,NewN)(J));
               --pragma Assert (for some J in 1 .. N-I-1 => not (for some K in 1 .. N-I => NewL.List(K) = J));
               pragma Assert (for some J in 1 .. N-I-1 => (for all K in 1 .. N-I => NewL.List(K) /= J));
               pragma Assert (for some J in 1 .. N-I-1 => (for all K in 1 .. N-I => List(K) /= J));
               NewL2 := ArgList'(Size => N-I-1, List => List);
               --pragma Assert (NewL.Size <= MaxNumberOfArgs);
               --pragma Assert (for all I in 1 .. NewL.Size => (NewL.List(I) /= 0 and not (for some J in 1 .. NewL.Size => (J /= I and NewL.List(J) = NewL.List(I)))));
               --pragma Assert (for all I in NewL.Size+1 .. MaxNumberOfArgs => NewL.List(I) = 0);
               NewN := N-I-1;
               --pragma Assert (for some K in 1 .. N-I => NewL.List(K) = N-I);
               --pragma Assert (NewL.List(N-I) /= N-I);
               --pragma Assert (for some K in 1 .. N-I-1 => NewL.List(K) = N-I);
               pragma Assert (for some J in 1 .. N-I-1 => (for all K in 1 .. N-I-1 => NewL2.List(K) /= J));
               pragma Assert (for some a in 1 .. N-I-1 => not ArgSet_From_ArgList(NewL2,NewN)(a));
               NewL := NewL2;
            end if;
         end loop;

         --pragma Assert (for all a in 1.. N => ArgSet_From_ArgList(L,N)(a));
      end if;
      
   end ArgList_Not_Full;




   procedure Quantificational_Reasoning (N : AFSize; L1 : ArgList; L2 : ArgList) is
   begin
      if (for all a in 1 .. N => not ArgSet_From_ArgList(L2,N)(a)) then
         for a in 1 .. N loop
            pragma Assert (not ArgSet_From_ArgList(L2,N)(a));
            pragma Assert (for all K in 1 .. N => L2.List(K) /= a);
            -- TODO: Continue here!

   end Quantificational_Reasoning;
      
     

   procedure Superset_Defends (S1 : ArgSet; S2 : ArgSet; a : Arg; F : AF) is
   begin
      null;
   end Superset_Defends;
      
      


   function ArgSet_Up_To (S : ArgSet; N : AFSize) return ArgSet is
      R : ArgSet := (1 .. MaxNumberOfArgs => False);
   begin

      for I in 1 .. N loop
         pragma Loop_Invariant (for all J in 1 .. I-1 => (if S(J) then R(J)));
         pragma Loop_Invariant (for all J in I .. MaxNumberOfArgs => not R(J));
         pragma Loop_Invariant (for all J in 1 .. MaxNumberOfArgs => (if R(J) then S(J)));
         R(I) := S(I);
      end loop;
      return R;

   end ArgSet_Up_To;


   function ArgSet_Size_Comparison (S1 : ArgSet; S2 : ArgSet) return NaturalPair is
      N1 : Natural := 0;
      N2 : Natural := 0;
   begin

      ArgSets_Up_To_0_Identical(S1,S2);
      for I in 1 .. MaxNumberOfArgs loop
         pragma Loop_Invariant (N1 <= I);
         pragma Loop_Invariant (N2 <= I);
         pragma Loop_Invariant (N1 <= N2);
         pragma Loop_Invariant (if N1 = N2 then ArgSet_Up_To(S1,I-1) = ArgSet_Up_To(S2,I-1));
         if S1(I) then
            N1 := N1+1;
         end if;
         if S2(I) then
            N2 := N2+1;
         end if;
         if N1 = N2 then
            ArgSets_Up_To_Identity_Induction_Step(S1,S2,I);
         end if;
      end loop;
      -- pragma Assert (N1 <= N2);
      pragma Assert (if N1 = N2 then ArgSet_Up_To(S1,MaxNumberOfArgs) = ArgSet_Up_To(S2,MaxNumberOfArgs));
      pragma Assert (if N1 = N2 then S1 = S2);

      return (N1,N2);

   end ArgSet_Size_Comparison;
      
      
      
   procedure ArgSets_Up_To_0_Identical (S1 : ArgSet; S2 : ArgSet) is
   begin

      null;

   end;


   procedure ArgSets_Up_To_Identity_Induction_Step (S1 : ArgSet; S2 : ArgSet; N : Positive) is
   begin

      null;

   end; 
