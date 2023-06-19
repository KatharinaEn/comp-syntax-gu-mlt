--# -path=.:../abstract
concrete MicroLangGer of MicroLang = open MicroResGer in {

-----------------------------------------------------
---------------- Grammar part -----------------------
-----------------------------------------------------

  lincat
    Utt = {s : Str} ;
    
    S  = {s : Str} ;
    VP = {verb : Verb ; compl : Declension => NumberGender => Case => Str} ;
    Pron = {s : Case => Str; g: Gender; n: Number; p: Person} ; 
    Det = {s: Gender => Case => Str; n: Number} ;
    Prep = {s : Str ; c : Case } ; 
    V = Verb ;
    V2 = Verb2 ;
    N,CN = Noun;
    NP = {s : Case => Str ; n: Number; p: Person } ; 
    Adv = {s : Str} ;
    A,AP,Comp = Adjective ;


   lin
    UttS s = s ;
    UttNP np = {s = np.s ! Acc} ;
 
    
    PredVPS np vp = {s = np.s ! Nom ++ vp.verb.s ! VPresT np.p np.n ++ vp.compl ! Pred ! SgAdj Masc ! Nom} ;  -- PredVPS   : NP -> VP -> S --John walks

    UseV v = { verb = v ; compl = \\d,ng,c =>[] } ; -- sleep -- V -> VP
      
    
    ComplV2 v2 np = { verb = v2 ; compl = \\d,ng,_ => v2.c } ;  -- V2 -> NP -> VP    -- love it -- Verb2 : Type = Verb ** {c : Str} ;
  

    UseComp comp = { verb = be_Verb ; compl = \\d,ng,c => comp.s ! Pred ! ng ! c } ;  -- Comp  -> VP -- be_Verb -> Verb (Verb : Type = {s : VForm => Str}) -- VForm = Inf | VPresT Person Number

    CompAP ap = ap ; 

    AdvVP vp adv =                --sleep here         -- VP -> Adv -> VP       
      vp ** {Comp = \\a => vp.Comp ! a ++ adv.s} ;  


    DetCN det cn = {            -- Det -> CN -> NP ;
    s = \\c => det.s ! cn.g ! c ;
    g = cn.g;
    n = det.n;
    p = P3 ; 
    } ;

   UsePron p = {s = p.s ; n = p.n ; p = p.p } ; -- p = Pron = pronoun 
   
  a_Det = {s = table {Masc => table{          Nom => "ein" ;
                                              Gen => "eines" ;
                                              Dat => "einem" ;
                                              Acc => "einen" 
                                              } ;
                      
                      Fem => table{           Nom => "eine" ;
                                              Gen => "einer" ;
                                              Dat => "einer" ;
                                              Acc => "eine" 
                                              } ;
                      
                      Neut => table{          Nom => "ein" ;
                                              Gen => "eines" ;
                                              Dat => "einem" ;
                                              Acc => "ein" 
                                              } 
                      } ;
          n = Sg; };          

   aPl_Det = {s = table {
		 _ => table {
       _ => ""
     }
    };
    n = Pl;
    };


      the_Det = {s = table {Masc => table 
                                {Nom => "der" ; 
                                Gen => "des" ;
                                Dat => "dem" ;
                                Acc => "den" } ;
                          Fem => table 
                                {Nom => "die" ;
                                Gen => "der" ;
                                Dat => "der" ;
                                Acc => "die" } ;
                           Neut => table 
                                {Nom => "das" ;
                                Gen => "des" ;
                                Dat => "dem" ;
                                Acc => "das" }} ;
                n = Sg }; -- n = Sg;

      thePl_Det = {s = table {Masc => table 
                            {Nom => "die" ; 
                            Gen => "der" ;
                            Dat => "den" ;
                            Acc => "die" } ;
                      Fem => table 
                            {Nom => "die" ;
                            Gen => "der" ;
                            Dat => "den" ;
                            Acc => "die" } ;
                        Neut => table 
                            {Nom => "die" ;
                            Gen => "der" ;
                            Dat => "den" ;
                            Acc => "die" }};
                n = Pl }; --n = Pl;

  UseN n = n ;


 AdjCN ap cn = {     -- AP -> CN -> CN    "big house"  
     s = \\n,c =>
      ap.s ! Strong ! (case n of {Pl => PlAdj;  
                        Sg => SgAdj cn.g }) ! c 
                        ++ cn.s ! n ! c; 
      g = cn.g 
      } ; 
  
  
    PositA a = a ;

     PrepNP prep c = {
      s = prep.s ; -- mit ihm: dat, auf ihn: acc
      } ;

    in_Prep = {
      s = "in" ;
      c = Dat ; 
      } ;

    on_Prep = {
      s = "auf" ;
      c = Acc ; 
      } ;

    with_Prep = {
      s = "mit" ;
      c = Dat ; 
    } ;

    he_Pron = {
      s = table {Nom => "er" ; Acc => "ihn"; Dat => "ihm"; Gen => "seiner"} ;
      g = Masc ;
      n = Sg ;
      p = P3 
      } ;
    she_Pron = {
      s = table {Nom => "sie" ; Acc => "sie"; Dat => "ihr"; Gen => "ihrer"} ;
      g = Masc ;
      n = Sg ; 
      p = P3 
      } ;
    they_Pron = {
      s = table {Nom => "sie" ; Acc => "sie"; Dat => "ihnen"; Gen => "ihrer"} ;
      g = Neut ;
      n = Pl ; 
      p = P3 
      } ;
      

-----------------------------------------------------
---------------- Lexicon part -----------------------
-----------------------------------------------------

lin already_Adv = mkAdv "schon" ;
lin animal_N = mkN "Tier" Neut ;
lin apple_N = mkN "Apfel" "Äpfel" Masc ;
lin baby_N = mkN "Baby" Neut ;
lin bad_A = mkA "schlecht" ;
lin beer_N = mkN "Bier" Neut ;
lin big_A = mkA "groß" ;
lin bike_N = mkN "Fahrrad" Neut ;
lin bird_N = mkN "Vogel" "Vögel" Masc ;
lin black_A = mkA "schwarz" ;
lin blood_N = mkN "Blut" Neut ;
lin blue_A = mkA "blau" ;
lin boat_N = mkN "Boot" Neut ;
lin book_N = mkN "Buch" "Bücher" Neut ;
lin boy_N = mkN "Junge" Masc ;
lin bread_N = mkN "Brot" Neut ;
lin break_V2 = mkV2 "brechen" "brechen" ;
lin buy_V2 = mkV2 "kaufen" "kaufen" ;
lin car_N = mkN "Auto" Neut ;
lin cat_N = mkN "Katze" Fem ;
lin child_N = mkN "Kind" "Kinder" Neut ;
lin city_N = mkN "Stadt" "Städte" Fem ;
lin clean_A = mkA "sauber" ;
lin clever_A = mkA "schlau" ;
lin cloud_N = mkN "Wolke" Fem ;
lin cold_A = mkA "kalt" ;
lin come_V = mkV "kommen" ;
lin computer_N = mkN "Computer" Masc ;
lin cow_N = mkN "Kuh" "Kühe" Fem  ;
lin dirty_A = mkA "schmutzig" ;
lin dog_N = mkN "Hund" Masc ;
lin drink_V2 = mkV2 "trinken" "trinken" ;
lin eat_V2 = mkV2 "essen" "essen" ;
lin find_V2 = mkV2 "finden" "finden" ;
lin fire_N = mkN "Feuer" Neut ;
lin fish_N = mkN "Fisch" Masc;
lin flower_N = mkN "Blume" Fem ;
lin friend_N = mkN "Freund" Masc ;
lin girl_N = mkN "Mädchen" "Mädchen" Neut ;
lin good_A = mkA "gut" ;
lin go_V = mkV "gehen" "gehen" "gehe" "gehst" "geht" "gehen" "geht" "gehen" ;
lin grammar_N = mkN "Grammatik" Fem ;
lin green_A = mkA "grün" ;
lin heavy_A = mkA "schwer" ;
lin horse_N = mkN "Pferd" Neut ;
lin hot_A = mkA "heiß" ;
lin house_N = mkN "Haus" "Häuser" Neut ;
-- lin john_PN = mkPN "John" ;
lin jump_V = mkV "springen" "springen" "springe" "springst" "springt" "springen" "springt" "springen" ;
lin kill_V2 = mkV2 "töten" ;
-- lin know_VS = mkVS (mkV "wissen") ;
lin language_N = mkN "Sprache" Fem ;
lin live_V = mkV "leben" ;
lin love_V2 = mkV2 "lieben" "lieben" ;
lin man_N = mkN "Mann" "Männer" Masc;
lin milk_N = mkN "Milch" Fem ;
lin music_N = mkN "Musik" Fem ;
lin new_A = mkA "neu" ;
lin now_Adv = mkAdv "jetzt" ;
lin old_A = mkA "alt" ;
-- lin paris_PN = mkPN "Paris" ;
lin play_V = mkV "spielen" ;
lin read_V2 = mkV2 "lesen" "lesen" ;
lin ready_A = mkA "bereit" ;
lin red_A = mkA "rot" ;
lin river_N = mkN "Fluss" "Flüsse" Masc ;
lin run_V = mkV "laufen" ;
lin sea_N = mkN "Meer" Neut ;
lin see_V2 = mkV2 "sehen" "sehen" ;
lin ship_N = mkN "Schiff" Neut ;
lin sleep_V = mkV "schlafen" ;
lin small_A = mkA "klein" ;
lin star_N = mkN "Stern" Masc;
lin swim_V = mkV "schwimmen" ;
lin teach_V2 = mkV2 "lehren" "lehren" ;
--lin teach_V2 = mkV2 (mkV "waschen") ;
lin train_N = mkN "Zug" "Züge" Masc ;
lin travel_V = mkV "reisen" ;
lin tree_N = mkN "Baum" "Bäume" Masc ;
lin understand_V2 = mkV2 "verstehen" "verstehen" ;
lin wait_V2 = mkV2 "warten" "auf" ;
lin walk_V = mkV "gehen" ;
lin warm_A = mkA "warm" ;
lin water_N = mkN "Wasser" Neut ;
lin white_A = mkA "weiß" ;
lin wine_N = mkN "Wein" Masc ;
lin woman_N = mkN "Frau" "Frauen" Fem ;
lin yellow_A = mkA "gelb" ;
lin young_A = mkA "jung" ;

---------------------------
-- Paradigms part ---------
---------------------------

oper
  mkN = overload {
    mkN : Str -> Gender -> Noun   
      = \n,g -> lin N (smartNoun n g) ;
    mkN : Str -> Str -> Gender -> Noun  
      = \sg,pl,g -> lin N (irregNoun sg pl g) ;
    } ;

  mkA = overload {
    mkA : Str -> Adjective
      = \a -> lin A (mkAdjective a) ;
      };

  mkV = overload {
    mkV : (stem : Str) -> V  -- predictable verb, e.g. play-plays, cry-cries, wash-washes
      = \v -> lin V (smartVerb v) ;
    mkV : (inf,stem,sg1,sg2,sg3,pl1,pl2,pl3 : Str) -> V  -- irregular verb, e.g. drink-drank-drunk
      = \inf,stem,sg1,sg2,sg3,pl1,pl2,pl3 -> lin V (irregVerb inf stem sg1 sg2 sg3 pl1 pl2 pl3) ;
    } ;

 mkV2 = overload {
    mkV2 : Str -> V2                                              -- predictable verb with direct object, e.g. "wash"
      = \v   -> lin V2 (smartVerb v ** {c = []}); 
    mkV2 : Str -> Str -> V2                                      -- predictable verb with preposition, e.g. "wait - for"
      = \v,p -> lin V2 (smartVerb v ** {c = p}) ; 
    mkV2 : V -> V2                                                -- any verb with direct object, e.g. "drink"
      = \v   -> lin V2 (v ** {c = []}); 
    mkV2 : V -> Str -> V2                                         -- any verb with preposition
      = \v,p -> lin V2 ( v ** {c = p}); 
    } ; 


  mkAdv : Str -> Adv
    = \s -> lin Adv {s = s} ;
  
  
  mkPrep : Str -> Case -> Prep
    = \s,c -> lin Prep {s = s; c = c} ;


} ; 