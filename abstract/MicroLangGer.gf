--# -path=.:../abstract
concrete MicroLangGer of MicroLang = open MicroResGer in {

-----------------------------------------------------
---------------- Grammar part -----------------------
-----------------------------------------------------

  lincat
    Utt = {s : Str} ;
    
    S  = {s : Str} ;
    VP = {verb : Verb ; compl : Declension => NumberGender => Case => Str} ;
    Pron = {s : Case => Str; n: Number ; g: Gender } ; 
    Det = {s: Gender => Case => Str } ; 
    Prep = {s : Str ; c : Case } ; 
    V = Verb ;
    V2 = Verb2 ;
    N,CN = Noun;
    NP = {s : Case => Str } ; 
    Adv = {s : Str} ;
    A,AP,Comp = Adjective ;


   lin
    UttS s = s ;
    UttNP np = {s = np.s ! Acc} ;
    
    {-
    PredVPS np vp = {                      --- John walks
    s = case np.isPron of {
	  True => case np.n of { Sg => np.s ! Nom ; Pl => "" } ;
	  False => np.s ! Nom
	  } ++ vp.verb.s ! VPresT np.n P3 ++ vp.compl ! Pred 
    };
    -} 

    UseV v = {           --sleep      V --> VP      
    Verb = v ;                      -- Verb : Type = {s : VForm => Str} ;   -- VForm = Inf | VPresT Person Number ;
    compl = \\stem,n,c => ap.s ! Strong (case n of {Pl => PlAdj; Sg => SgAdj v.g }) ! c 
                        ++ v.s ! n ! c ++ v.s ! stem (case stem of {VPresT => Person Number}) ++ Inf ; 
                                    --  VP = {verb : Verb ; compl : UseAP => Str; isPron : Bool } ;
    --isPron = False 
    -- Adjective : Type = {s : Declension => NumberGender => Case => Str}
    } ;
      
    ComplV2 v2 np ap = {           -- V2 -> NP -> VP        -- love it                      
      Verb2 = v2 ;                                         -- Verb2 : Type = Verb ** {c : Gender => Number => Str} ; 
      compl = \\stem,n,c => v2.s ! stem (case stem of {VPresT => Person Number}) ++ Inf ++ ap.s ! Strong (case n of {Pl => PlAdj;  
                        Sg => SgAdj v2.g }) ! c 
                        ++ v2.s ! n ! c; 
      g = v2.g ;                                  -- NP = {s : Case => Str ; g : Gender ; n : Number; isPron : Bool} ; 
    --isPron = np.isPron                                  -- Adjective = {s : Declension => NumberGender => Case => Str}
	   } ;
    
    UseComp comp ap = {
      Verb = be_Verb ; -- be_Verb -> Verb (Verb : Type = {s : VForm => Str}) -- VForm = Inf | VPresT Person Number
      compl = \\n,c => comp.s ! Inf (case Inf of {VPresT => Person Number}) ++ Inf ++ ap.s ! Strong (case n of {Pl => PlAdj;  
                        Sg => SgAdj comp.g }) ! c 
                        ++ comp.s ! n ! c ++ c
      --g = cn.g ; 
      -- Comp  -> VP
      
      -- Declension = Strong | Weak | Mixed | Pred
      --isPron = False  -- comp = Adjective Adjective = {s : Declension => NumberGender => Case => Str}
    };

    CompAP ap = {s = \\Comp => ap.s ! Pred} ;

    AdvVP vp adv =                --sleep here         -- VP -> Adv -> VP       
      vp ** {Comp = \\a => vp.Comp ! a ++ adv.s} ;  


    DetCN det cn = {            -- Det -> CN -> NP ;
    s = \\c => det.s ! cn.g ! c ;
    g = cn.g;
    n = det.n;
    } ;

   UsePron p = {s = p.s } ;
   
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
                 }; -- n = Sg;

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
                 }; --n = Pl;

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
      n = Sg
      } ;
    she_Pron = {
      s = table {Nom => "sie" ; Acc => "sie"; Dat => "ihr"; Gen => "ihrer"} ;
      g = Masc ;
      n = Sg
      } ;
    they_Pron = {
      s = table {Nom => "sie" ; Acc => "sie"; Dat => "ihnen"; Gen => "ihrer"} ;
      g = Neut ;
      n = Pl
      } ;
      

-----------------------------------------------------
---------------- Lexicon part -----------------------
-----------------------------------------------------

lin already_Adv = mkAdv "schon" ;
lin animal_N = mkN "Tier" ;
lin apple_N = mkN "Apfel" "Äpfel" Masc ;
lin baby_N = mkN "Baby" ;
lin bad_A = mkA "schlecht" ;
lin beer_N = mkN "Bier" ;
lin big_A = mkA "groß" ;
lin bike_N = mkN "Fahrrad" ;
lin bird_N = mkN "Vogel" "Vögel" Masc ;
lin black_A = mkA "schwarz" ;
lin blood_N = mkN "Blut" ;
lin blue_A = mkA "blau" ;
lin boat_N = mkN "Boot" ;
lin book_N = mkN "Buch" "Bücher" Neut ;
lin boy_N = mkN "Junge" ;
lin bread_N = mkN "Brot" ;
lin break_V2 = mkV2 (mkV "brechen" "brach" "gebrochen") ;
lin buy_V2 = mkV2 (mkV "kauften" "kaufte" "gekauft") ;
lin car_N = mkN "Auto" ;
lin cat_N = mkN "Katze" ;
lin child_N = mkN "Kind" "Kinder" Neut ;
lin city_N = mkN "Stadt" "Städte" Fem ;
lin clean_A = mkA "sauber" ;
lin clever_A = mkA "schlau" ;
lin cloud_N = mkN "Wolke" ;
lin cold_A = mkA "kalt" ;
lin come_V = mkV "kommen" "kam" "gekommen" ;
lin computer_N = mkN "Computer" ;
lin cow_N = mkN "Kuh" "Kühe" Fem  ;
lin dirty_A = mkA "schmutzig" ;
lin dog_N = mkN "Hund" ;
lin drink_V2 = mkV2 (mkV "trinken" "trank" "getrunken") ;
lin eat_V2 = mkV2 (mkV "essen" "aß" "gegessen") ;
lin find_V2 = mkV2 (mkV "finden" "fand" "gefunden") ;
lin fire_N = mkN "Feuer" ;
lin fish_N = mkN "Fisch" ;
lin flower_N = mkN "Blume" ;
lin friend_N = mkN "Freund" ;
lin girl_N = mkN "Mädchen" "Mädchen" Neut ;
lin good_A = mkA "gut" "besser" "am besten" ;
lin go_V = mkV "gehen" "ging" "gegangen" ;
lin grammar_N = mkN "Grammatik" ;
lin green_A = mkA "grün" ;
lin heavy_A = mkA "schwer" ;
lin horse_N = mkN "Pferd" ;
lin hot_A = mkA "heiß" ;
lin house_N = mkN "Haus" "Häuser" Neut ;
-- lin john_PN = mkPN "John" ;
lin jump_V = mkV "springen" ;
lin kill_V2 = mkV2 "töten" ;
-- lin know_VS = mkVS (mkV "wissen" "wusste" "gewusst") ;
lin language_N = mkN "Sprache" ;
lin live_V = mkV "leben" ;
lin love_V2 = mkV2 (mkV "lieben") ;
lin man_N = mkN "Mann" "Männer" ;
lin milk_N = mkN "Milch" ;
lin music_N = mkN "Musik" ;
lin new_A = mkA "neu" ;
lin now_Adv = mkAdv "jetzt" ;
lin old_A = mkA "alt" ;
-- lin paris_PN = mkPN "Paris" ;
lin play_V = mkV "spielen" ;
lin read_V2 = mkV2 (mkV "lesen" "las" "gelesen") ;
lin ready_A = mkA "bereit" ;
lin red_A = mkA "rot" ;
lin river_N = mkN "Fluss" "Flüsse" Masc ;
lin run_V = mkV "laufen" "lief" "gelaufen" ;
lin sea_N = mkN "Meer" ;
lin see_V2 = mkV2 (mkV "sehen" "sah" "gesehen") ;
lin ship_N = mkN "Schiff" ;
lin sleep_V = mkV "schlafen" "schlief" "geschlafen" ;
lin small_A = mkA "klein" ;
lin star_N = mkN "Stern" ;
lin swim_V = mkV "schwimmen" "schwamm" "geschommen" ;
lin teach_V2 = mkV2 (mkV "lehren" "lehrte" "gelehrt") ;
--lin teach_V2 = mkV2 (mkV "waschen" "wäschst" "gewaschen") ;
lin train_N = mkN "Zug" "Züge" Masc ;
lin travel_V = mkV "reisen" ;
lin tree_N = mkN "Baum" "Bäume" Masc ;
lin understand_V2 = mkV2 (mkV "verstehen" "verstanden" "verstanden haben") ;
lin wait_V2 = mkV2 "warten" "auf" ;
lin walk_V = mkV "gehen" "ging" "gegangen" ;
lin warm_A = mkA "warm" ;
lin water_N = mkN "Wasser" ;
lin white_A = mkA "weiß" ;
lin wine_N = mkN "Wein" ;
lin woman_N = mkN "Frau" "Frauen" ;
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
    mkV : (stem : Str) -> V  -- irregular verb, e.g. drink-drank-drunk
      = \v -> lin V (irregVerb v) ;
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