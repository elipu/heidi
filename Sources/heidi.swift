import LogicKit

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Abstract Syntax §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Abstract syntax: From Heidi ===========================
/*
  Commands = {davent,davos,deponer,dretg,plaun,returnar,sanester, saFermar}  (in Romansh)

   __________________
    comm ϵ Commands


     comm ϵ Commands , c ϵ List
   -------------------------------   (Sequence of Commands)
         comm :: c ϵ List

*/
// Commands:
let davent    = Value("davent")
let davos     = Value("davos")
let deponer   = Value("deponer")
let dretg     = Value("dretg")
let plaun     = Value("plaun")
let returnar  = Value("returnar")
let sanester  = Value("sanester")
let saFermar  = Value("sa fermar")

// ====================== Abstract syntax: From Tita ===========================
/*
  Whistles = {short,long,pause,hee,who,wheeo,whee,wheet}

   __________________
    whist ϵ Whistles


       whist ϵ Whistles\{pause} , w ϵ List
   -------------------------------------------   (Sequence of whistles = whistle command)
         whist :: w ϵ WhistleCommand

        whist ϵ WhistleCommand , p = pause , w ϵ WhistleCommand
   --------------------------------------------------------------    (Sequence of whistle commands = work session)
                  whist :: p :: w ϵ  WorkSession

    (pause is to distinguish between whistle commands)

*/
// Whistles:
let short   = Value("short")
let long    = Value("long")
let pause   = Value("pause")         // a pause is just a silent whistle ¯\_(ツ)_/¯
let hee     = Value("hee")
let who     = Value("who")
let wheeo   = Value("wheeo")
let whee    = Value("whee")
let wheet   = Value("wheet")

// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Semantics §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Semantics: Heidi to Tita ===========================
/*

    davent ϵ Commands , wheet::wheeo::wheet::wheet ϵ WhistleCommand
   ------------------------------------------------------------------
            davent ---HtoT---> wheet::wheeo::wheet::wheet


     davos ϵ Commands , who::hee::who ϵ WhistleCommand
    ----------------------------------------------------
            davos ---HtoT---> who::hee:who

      deponer ϵ Commands , short::short ϵ WhistleCommand
     -----------------------------------------------------
             deponer ---HtoT---> short::short

       dretg ϵ Commands , whee::who ϵ WhistleCommand
      ---------------------------------------------------
              dretg ---HtoT---> whee:who

      plaun ϵ Commands , hee::hee::hee::hee ϵ WhistleCommand
     ---------------------------------------------------------
             plaun ---HtoT---> hee::hee::hee::hee

       returnar ϵ Commands , whee::whee::wheet ϵ WhistleCommand
     -----------------------------------------------------------
              returnar ---HtoT---> whee::whee::wheet

      sanester ϵ Commands , whee:t:wheeo ϵ WhistleCommand
     -----------------------------------------------------
             sanester ---HtoT---> wheet::wheeo

     saFermar ϵ Commands , long ϵ WhistleCommand
    -------------------------------------------------
              saFermar ---HtoT---> long
*/

func HT_Davent(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.cons(pause, other)))))
}

func HT_Davos(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(who, List.cons(hee, List.cons(who, List.cons(pause, other))))
}

func HT_Deponer(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === deponer
            &&
         Whistle_output === List.cons(short, List.cons(short, List.cons(pause, other)))
}

func HT_Dretg(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === dretg
            &&
         Whistle_output === List.cons(whee, List.cons(who, List.cons(pause, other)))
}

func HT_Plaun(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === plaun
            &&
         Whistle_output === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.cons(pause, other)))))
}

func HT_Returnar(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === returnar
            &&
         Whistle_output === List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, other))))
}

func HT_Sanester(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === sanester
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(pause, other)))
}

func HT_SaFermar(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === saFermar
            &&
         Whistle_output === List.cons(long, List.cons(pause, other))
}

// ===================== Semantics: Tita to Heidi ===========================
/*

    wheet::wheeo::wheet::wheet ϵ WhistleCommand , davent ϵ Commands
   ------------------------------------------------------------------
            wheet::wheeo::wheet::wheet ---TtoH---> davent


     who::hee::who ϵ WhistleCommand , davos ϵ Commands
    ----------------------------------------------------
            who::hee:who ---TtoH---> davos

      short::short ϵ WhistleCommand , deponer ϵ Commands
     -----------------------------------------------------
            short::short ---TtoH---> deponer

        whee::who ϵ WhistleCommand , dretg ϵ Commands
      ---------------------------------------------------
              whee:who ---TtoH---> dretg

       hee::hee::hee::hee ϵ WhistleCommand , plaun ϵ Commands
     ----------------------------------------------------------
             hee::hee::hee::hee ---TtoH---> plaun

       whee::whee::wheet ϵ WhistleCommand , returnar ϵ Commands
      ----------------------------------------------------------
              whee::whee::wheet ---TtoH---> returnar

      whee:t:wheeo ϵ WhistleCommand , sanester ϵ Commands
     -----------------------------------------------------
            wheet::wheeo  ---TtoH---> sanester

      long ϵ WhistleCommand , saFermar ϵ Commands
    -------------------------------------------------
              long ---TtoH---> saFermar
*/

func TH_Davent(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.cons(pause, other)))))
            &&
         Command_output === davos
}

func TH_Davos(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(who, List.cons(hee, List.cons(who, List.cons(pause, other))))
            &&
         Command_output === davos
}

func TH_Deponer(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return  Whistle_input === List.cons(short, List.cons(short, List.cons(pause, other)))
            &&
          Command_output === deponer
}

func TH_Dretg(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(whee, List.cons(who, List.cons(pause, other)))
            &&
         Command_output === dretg
}

func TH_Plaun(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.cons(pause, other)))))
            &&
         Command_output === plaun
}

func TH_Returnar(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, other))))
            &&
         Command_output === returnar
}

func TH_Sanester(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(pause, other)))
            &&
         Command_output === sanester
}

func TH_SaFermar(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(long, List.cons(pause, other))
            &&
         Command_output === saFermar
}

// =========================== Translator =====================================

func Translate_HT(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === davent && HT_Davent(ch,Translation,tt) ||
                   ch === davos && HT_Davos(ch,Translation,tt) ||
                   ch === deponer && HT_Deponer(ch,Translation,tt) ||
                   ch === dretg && HT_Dretg(ch,Translation,tt) ||
                   ch === plaun && HT_Plaun(ch,Translation,tt) ||
                   ch === returnar && HT_Returnar(ch,Translation,tt) ||
                   ch === sanester && HT_Sanester(ch,Translation,tt) ||
                   ch === saFermar && HT_SaFermar(ch,Translation,tt)
                      &&
                   delayed(Translate_HT(ch,Translation,tt))
                 )}
}


func Translate_TH(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.cons(pause, List.empty))))) && TH_Davent(ch,Translation,tt) ||
                   ch === List.cons(who, List.cons(hee, List.cons(who, List.cons(pause, List.empty)))) && TH_Davos(ch,Translation,tt) ||
                   ch === List.cons(short, List.cons(short, List.cons(pause, List.empty))) && TH_Deponer(ch,Translation,tt) ||
                   ch === List.cons(whee, List.cons(who, List.cons(pause, List.empty))) && TH_Dretg(ch,Translation,tt) ||
                   ch === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.cons(pause, List.empty))))) && TH_Plaun(ch,Translation,tt) ||
                   ch === List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, List.empty)))) && TH_Returnar(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(pause, List.empty))) && TH_Sanester(ch,Translation,tt) ||
                   ch === List.cons(long, List.cons(pause, List.empty)) && TH_SaFermar(ch,Translation,tt)
                   &&
                   delayed(Translate_TH(ch,Translation,tt))
                 )}
}

func Translate(_ Command: Term, _ Translation: Term) {

  return Translate_HT(Command, Translation)
                    ||
         Translate_TH(Command, Translation)

}

// ##########################################################################################################
// ##########################################################################################################
// ############################################## Optimisation ##############################################
// ##########################################################################################################
// ##########################################################################################################

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Abstract Syntax §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// Same abstract syntaxes, except for the set Whistles:
// Whistles = {hee,wheet,wheeo,pause}

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Semantics §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Semantics: Heidi to Tita ===========================
/*

    davent ϵ Commands , wheet::hee::wheet ϵ WhistleCommand
   ------------------------------------------------------------------
            davent ---HtoT---> wheet::hee::wheet


     davos ϵ Commands , wheet::wheeo:wheet ϵ WhistleCommand
    ----------------------------------------------------
            davos ---HtoT---> wheet::wheeo:wheet

      deponer ϵ Commands , wheeo::hee::wheet ϵ WhistleCommand
     -----------------------------------------------------
             deponer ---HtoT---> wheeo::hee::wheet

       dretg ϵ Commands , hee::wheet ϵ WhistleCommand
      ---------------------------------------------------
              dretg ---HtoT---> hee::wheet

      plaun ϵ Commands , wheet::wheeo::wheeo ϵ WhistleCommand
     ---------------------------------------------------------
             plaun ---HtoT---> wheet::wheeo::wheeo

       returnar ϵ Commands , wheeo::wheet ϵ WhistleCommand
      ----------------------------------------------------------
              returnar ---HtoT---> wheeo::wheet

      sanester ϵ Commands , wheet::wheeo ϵ WhistleCommand
     -----------------------------------------------------
             sanester ---HtoT---> wheet::wheeo

     saFermar ϵ Commands , wheeo::wheeo ϵ WhistleCommand
    -------------------------------------------------
              saFermar ---HtoT---> wheeo::wheeo
*/

func HT_Davent_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(wheet, List.cons(hee, List.cons(wheet, List.cons(pause, other))))
}

func HT_Davos_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other))))
}

func HT_Deponer_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === deponer
            &&
         Whistle_output === List.cons(wheeo, List.cons(hee, List.cons(wheet, List.cons(pause, other))))
}

func HT_Dretg_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === dretg
            &&
         Whistle_output === List.cons(hee, List.cons(wheet, List.cons(pause, other)))
}

func HT_Plaun_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === plaun
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other))))
}

func HT_Returnar_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === returnar
            &&
         Whistle_output === List.cons(wheeo, List.cons(wheet, List.cons(pause, other)))
}

func HT_Sanester_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === sanester
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(pause, other)))
}

func HT_SaFermar_opt(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === saFermar
            &&
         Whistle_output === List.cons(wheeo, List.cons(wheeo, List.cons(pause, other)))
}

// ===================== Semantics: Tita to Heidi ===========================
/*

    wheet::hee::wheet ϵ WhistleCommand , davent ϵ Commands
   ---------------------------------------------------------
            wheet::hee::wheet ---TtoH---> davent


     wheet::wheeo:wheet ϵ WhistleCommand , davos ϵ Commands
    ---------------------------------------------------------
            wheet::wheeo:wheet ---TtoH---> davos

      wheeo::hee::wheet ϵ WhistleCommand , deponer ϵ Commands
     ---------------------------------------------------------
            wheeo::hee::wheet ---TtoH---> deponer

        hee::wheet ϵ WhistleCommand , dretg ϵ Commands
      ---------------------------------------------------
              hee::wheet ---TtoH---> dretg

       wheet::wheeo::wheeo ϵ WhistleCommand , plaun ϵ Commands
     -----------------------------------------------------------
             wheet::wheeo::wheeo ---TtoH---> plaun

       wheeo::wheet ϵ WhistleCommand , returnar ϵ Commands
      -------------------------------------------------------
              wheeo::wheet ---TtoH---> returnar

      wheet::wheeo ϵ WhistleCommand , sanester ϵ Commands
     ------------------------------------------------------
            wheet::wheeo  ---TtoH---> sanester

      wheeo::wheeo ϵ WhistleCommand , saFermar ϵ Commands
    -------------------------------------------------------
              wheeo::wheeo ---TtoH---> saFermar
*/

func TH_Davent_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(hee, List.cons(wheet, List.cons(pause, other))))
            &&
         Command_output === davos
}

func TH_Davos_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other))))
            &&
         Command_output === davos
}

func TH_Deponer_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return  Whistle_input === List.cons(wheeo, List.cons(hee, List.cons(wheet, List.cons(pause, other))))
            &&
          Command_output === deponer
}

func TH_Dretg_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(hee, List.cons(wheet, List.cons(pause, other)))
            &&
         Command_output === dretg
}

func TH_Plaun_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other))))
            &&
         Command_output === plaun
}

func TH_Returnar_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheeo, List.cons(wheet, List.cons(pause, other)))
            &&
         Command_output === returnar
}

func TH_Sanester_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(pause, other)))
            &&
         Command_output === sanester
}

func TH_SaFermar_opt(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheeo, List.cons(wheeo, List.cons(pause, other)))
            &&
         Command_output === saFermar
}

/*

func Translate_HT_opt(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === davent && HT_Davent_opt(ch,Translation,tt) ||
                   ch === davos && HT_Davos_opt(ch,Translation,tt) ||
                   ch === deponer && HT_Deponer_opt(ch,Translation,tt) ||
                   ch === dretg && HT_Dretg_opt(ch,Translation,tt) ||
                   ch === plaun && HT_Plaun_opt(ch,Translation,tt) ||
                   ch === returnar && HT_Returnar_opt(ch,Translation,tt) ||
                   ch === sanester && HT_Sanester_opt(ch,Translation,tt) ||
                   ch === saFermar && HT_SaFermar_opt(ch,Translation,tt)
                      &&
                   delayed(Translate_HT_opt(ch,Translation,tt))
                 )}
}


func Translate_TH_opt(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === List.cons(wheet, List.cons(hee, List.cons(wheet, List.cons(pause, other)))) && TH_Davent_opt(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other)))) && TH_Davos_opt(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(hee, List.cons(wheet, List.cons(pause, other)))) && TH_Deponer_opt(ch,Translation,tt) ||
                   ch === List.cons(hee, List.cons(wheet, List.cons(pause, other))) && TH_Dretg_opt(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(pause, other)))) && TH_Plaun_opt(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(wheet, List.cons(pause, other))) && TH_Returnar_opt(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(pause, other))) && TH_Sanester_opt(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(wheeo, List.cons(pause, other))) && TH_SaFermar_opt(ch,Translation,tt)
                   &&
                   delayed(Translate_TH_opt(ch,Translation,tt))
                 )}
}

func Translate_opt(_ Command: Term, _ Translation: Term) {

  return Translate_HT_opt(Command, Translation)
                    ||
         Translate_TH_opt(Command, Translation)

}

*/

/*
// ##########################################################################################################
// ##########################################################################################################
// ################################################# Proof ##################################################
// ##########################################################################################################
// ##########################################################################################################
---------------------------------
--Prouvez que les ordres donnés en romanche par Heidi sont bien executés par Tita, c'est-à-dire que
--la traduction romanche vers sifflets vers romanche retourne le programme d'origine.
---------------------------------

To prove that the translation romansh-whistle-romansh returns the source, we proceed by induction:

  § 0 commands

    source = [] ---HtoT---> whistle = [] ---TtoH---> romansh = []

  § 1 command

    source = [sanester] ---HtoT---> whistle = [wheet::wheeo] ---TtoH---> romansh = [sanester]

    By replacing the source with any command we can prove that a sequence of 1 command will always be true without ambiguity.

  Let's suppose that any sequence with (n-1) commands return true without any ambiguity, and let's prove for (n) commands:

    The command sequence would look like, at the nth command: [((n-1)ProvenCommand::pause)::(nthCommand::pause)::(rest::pause)]

    We can easily see that evaluating the nth command is like evalutating a single command which we proved just above.

    So by the inductive hypothesis, the nth command will be true withouht ambihuity.

    ((Every element of a sequence of Roamnsh commands is a single Romansh command, so they are clearly separated.
      And, every command in a sequence of whistle commands are clearly separated by a pause.
      Thus, commands in every language are separated without any ambiguity))
*/
/*
// ##########################################################################################################
// ##########################################################################################################
// ############################################## Acceleration ##############################################
// ##########################################################################################################
// ##########################################################################################################
---------------------------------
--Au bout de quelques jours à diriger Tita, Heidi prend confiance et réduit de plus en plus les pauses
--entre ses ordres. Arrive le moment où elle supprime totalement ces pauses.

--Évaluez (romanche vers sifflets vers romanche) le programme suivant :

--    plaun
--    dretg
--    plaun
--    deponer
--    sa fermar

--Que remarquez-vous ?
---------------------------------

The code is below but there are no tests to execute the code, where the evalutation is accelerated which means that
there are no pauses in between whistle commands.

Executing
  Translate_acc([plaun::dretg::plaun::deponer::saFermar], Translation)
returns
  Translation = [wheet::wheeo::wheeo::hee::wheet::wheet::wheeo::wheeo::wheeo::hee::wheet::wheeo::wheeo]

But Translation can be re-translated in 4 different command sequences:
  Executing
    Translate_acc([wheet::wheeo::wheeo::hee::wheet::wheet::wheeo::wheeo::wheeo::hee::wheet::wheeo::wheeo], reTranslation)
  returns
    reTranslation = [plaun::dretg::sanester::saFermar::dretg::saFermar]
      ||
    reTranslation = [plaun::dretg::plaun::deponer::saFermar]
      ||
    reTranslation = [sanester::deponer::sanester::saFermar::dretg::saFermar]
      ||
    reTranslation = [sanester::deponer::plaun::deponer::saFermar]

Among these 4 sequences only one of the reTranslation evaluations ties in with the original command sequence.

*/

/*
----Heidi----
func HT_Davent_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(wheet, List.cons(hee, List.cons(wheet, other)))
}

func HT_Davos_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === davos
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, other)))
}

func HT_Deponer_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === deponer
            &&
         Whistle_output === List.cons(wheeo, List.cons(hee, List.cons(wheet, other)))
}

func HT_Dretg_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === dretg
            &&
         Whistle_output === List.cons(hee, List.cons(wheet, other))
}

func HT_Plaun_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === plaun
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, other)))
}

func HT_Returnar_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === returnar
            &&
         Whistle_output === List.cons(wheeo, List.cons(wheet, other))
}

func HT_Sanester_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === sanester
            &&
         Whistle_output === List.cons(wheet, List.cons(wheeo, other))
}

func HT_SaFermar_acc(_ Command_input: Term, _ Whistle_output: Term, _ other: Term) -> Goal {

  return Command_input === saFermar
            &&
         Whistle_output === List.cons(wheeo, List.cons(wheeo, other))
}

------Tita------
func TH_Davent_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(hee, List.cons(wheet, other)))
            &&
         Command_output === davos
}

func TH_Davos_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, other)))
            &&
         Command_output === davos
}

func TH_Deponer_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return  Whistle_input === List.cons(wheeo, List.cons(hee, List.cons(wheet, other)))
            &&
          Command_output === deponer
}

func TH_Dretg_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(hee, List.cons(wheet, other))
            &&
         Command_output === dretg
}

func TH_Plaun_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, other)))
            &&
         Command_output === plaun
}

func TH_Returnar_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheeo, List.cons(wheet, other))
            &&
         Command_output === returnar
}

func TH_Sanester_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheet, List.cons(wheeo, other))
            &&
         Command_output === sanester
}

func TH_SaFermar_acc(_ Whistle_input: Term, _ Command_output: Term, _ other: Term) -> Goal {

  return Whistle_input === List.cons(wheeo, List.cons(wheeo, other))
            &&
         Command_output === saFermar
}


func Translate_HT_acc(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === davent && HT_Davent_acc(ch,Translation,tt) ||
                   ch === davos && HT_Davos_acc(ch,Translation,tt) ||
                   ch === deponer && HT_Deponer_acc(ch,Translation,tt) ||
                   ch === dretg && HT_Dretg_acc(ch,Translation,tt) ||
                   ch === plaun && HT_Plaun_acc(ch,Translation,tt) ||
                   ch === returnar && HT_Returnar_acc(ch,Translation,tt) ||
                   ch === sanester && HT_Sanester_acc(ch,Translation,tt) ||
                   ch === saFermar && HT_SaFermar_acc(ch,Translation,tt)
                      &&
                   delayed(Translate_HT_acc(ch,Translation,tt))
                 )}
}


func Translate_TH_acc(_ Command: Term, _ Translation: Term) {

  return (Command === List.empty && Translation === List.empty) ||

         freshn { l in let ch = l["ch"]
                       let ct = l["ct"]
                       let tt = l["tt"]

                 (Command === List.cons(ch,ct)) &&
                 (
                   ch === List.cons(wheet, List.cons(hee, List.cons(wheet, other))) && TH_Davent_acc(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, ist.cons(wheet, other))) && TH_Davos_acc(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(hee, List.cons(wheet, other))) && TH_Deponer_acc(ch,Translation,tt) ||
                   ch === List.cons(hee, List.cons(wheet, other)) && TH_Dretg_acc(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, List.cons(wheet, other))) && TH_Plaun_acc(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(wheet, other)) && TH_Returnar_acc(ch,Translation,tt) ||
                   ch === List.cons(wheet, List.cons(wheeo, other)) && TH_Sanester_acc(ch,Translation,tt) ||
                   ch === List.cons(wheeo, List.cons(wheeo, other)) && TH_SaFermar_acc(ch,Translation,tt)
                   &&
                   delayed(Translate_TH_acc(ch,Translation,tt))
                 )}
}

func Translate_acc(_ Command: Term, _ Translation: Term) {

  return Translate_HT_acc(Command, Translation)
                    ||
         Translate_TH_acc(Command, Translation)

}
*/

/*
// ##########################################################################################################
// ##########################################################################################################
// ################################################ Problems ################################################
// ##########################################################################################################
// ##########################################################################################################
---------------------------------
--Est-il possible d'obtenir la liste de tous les problèmes possibles ? Si non, pourquoi ?
--Si oui, comment (et donnez alors le code le permettant) ?
---------------------------------
The more the command sequence have commands, the more there will be ambiguity.

Thus, in my opinion, the possibility of getting a list of every possible problem decreases when the number of
commands increases. And this can be proven by repeating, the sequence given above, multiple times.
*/
