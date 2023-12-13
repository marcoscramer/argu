package body Core_Functions_And_Theorems with
   Spark_Mode
is


   function Find_Grounded (F : AF) return ArgSet is
      --R : ArgSet := (1 .. MaxNumberOfArgs => False);
      L : ArgList := ArgList'(Size => 0, List => (1 .. MaxNumberOfArgs => 0));
      Searching : Boolean := True;
      SR : SearchResult;
   begin

      pragma Assert (not (for some I in 1 .. MaxNumberOfArgs => ArgSet_From_ArgList(L,F.Size)(I)));
      pragma Assert (Is_ArgList_For(L,F.Size));
      while Searching loop
         pragma Loop_Variant (Increases => L.Size);
         --pragma Loop_Invariant (Is_ArgSet(R,F));
         pragma Loop_Invariant (Is_ArgList_For(L,F.Size));
         pragma Loop_Invariant (Admissible(ArgSet_From_ArgList(L,F.Size),F));
         pragma Loop_Invariant (for all I in Arbitrary_ArgSets(F.Size)'Range => (if Complete(Arbitrary_ArgSets(F.Size)(I),F) then Subset(ArgSet_From_ArgList(L,F.Size),Arbitrary_ArgSets(F.Size)(I))));
         SR := Lemmas.Search_Acceptable_Arg(ArgSet_From_ArgList(L,F.Size),F);
         Searching := SR.Exists;
         if SR.Exists = True then
            Lemmas.Every_Complete_Extension_Contains(SR.Arg,ArgSet_From_ArgList(L,F.Size),F);
            Lemmas.Extend_Admissible_List(L,SR.Arg,F);
         end if;
      end loop;

      --return R;
      return ArgSet_From_ArgList(L,F.Size);

   end Find_Grounded;


   procedure Exists_Unique_Grounded (F : AF) is
      S : ArgSet;
      I : Positive;
   begin

      S := Find_Grounded(F);
      I := Exists_ArgSet_Intro(F.Size,S);
      Lemmas.Grounded_by_Equality(S,Arbitrary_ArgSets(F.Size)(I),F);
      for K in Arbitrary_ArgSets(F.Size)'Range loop
         pragma Loop_Invariant (for all J in Arbitrary_ArgSets(F.Size)'First .. K-1 => (if Grounded(Arbitrary_ArgSets(F.Size)(J),F) then Arbitrary_ArgSets(F.Size)(I) = Arbitrary_ArgSets(F.Size)(J)));
         if Grounded(Arbitrary_ArgSets(F.Size)(K),F) then
            pragma Assert (Subset(Arbitrary_ArgSets(F.Size)(I),Arbitrary_ArgSets(F.Size)(K)));
            pragma Assert (Arbitrary_ArgSets(F.Size)(I) = Arbitrary_ArgSets(F.Size)(K));
         end if;
      end loop;
      pragma Assert (for all K in Arbitrary_ArgSets(F.Size)'Range => (if Grounded(Arbitrary_ArgSets(F.Size)(K),F) then Arbitrary_ArgSets(F.Size)(I) = Arbitrary_ArgSets(F.Size)(K)));

   end Exists_Unique_Grounded;


   procedure Exists_Preferred (F : AF) is
      S : ArgSet;
      I : Positive;
   begin

      S := Find_Grounded(F);
      I := Exists_ArgSet_Intro(F.Size,S);
      pragma Assert (I in Arbitrary_ArgSets(F.Size)'Range);
      --pragma Assert (Complete(S,F));
      --pragma Assert (S = Arbitrary_ArgSets(F.Size)(I));
      --pragma Assert (Complete(Arbitrary_ArgSets(F.Size)(I),F));
      Lemmas.Complete_by_Equality(S,Arbitrary_ArgSets(F.Size)(I),F);
      for K in Arbitrary_ArgSets(F.Size)'Range loop
         pragma Loop_Invariant (I in Arbitrary_ArgSets(F.Size)'Range);
         pragma Loop_Invariant (Complete(Arbitrary_ArgSets(F.Size)(I),F));
         pragma Loop_Invariant (for all L in Arbitrary_ArgSets(F.Size)'First .. K-1 => (if Subset(Arbitrary_ArgSets(F.Size)(I),Arbitrary_ArgSets(F.Size)(L)) and Complete(Arbitrary_ArgSets(F.Size)(L),F) then Arbitrary_ArgSets(F.Size)(I) = (Arbitrary_ArgSets(F.Size)(L))));
         pragma Loop_Invariant (I in Arbitrary_ArgSets(F.Size)'Range);
         if Subset(Arbitrary_ArgSets(F.Size)(I),Arbitrary_ArgSets(F.Size)(K)) and Arbitrary_ArgSets(F.Size)(I) /= Arbitrary_ArgSets(F.Size)(K) and Complete(Arbitrary_ArgSets(F.Size)(K),F) then
            I := K;
         end if;
         pragma Assert (if Subset(Arbitrary_ArgSets(F.Size)(I),Arbitrary_ArgSets(F.Size)(K)) and Complete(Arbitrary_ArgSets(F.Size)(K),F) then Arbitrary_ArgSets(F.Size)(I) = (Arbitrary_ArgSets(F.Size)(K)));
      end loop;
      pragma Assert (for all L in Arbitrary_ArgSets(F.Size)'Range => (if Subset(Arbitrary_ArgSets(F.Size)(I),Arbitrary_ArgSets(F.Size)(L)) and Complete(Arbitrary_ArgSets(F.Size)(L),F) then Arbitrary_ArgSets(F.Size)(I) = (Arbitrary_ArgSets(F.Size)(L))));
      --pragma Assert (Preferred(Arbitrary_ArgSets(F.Size)(I),F));

   end Exists_Preferred;



end Core_Functions_And_Theorems;
