# Revue indépendante : choix ouvert/fermé, 5 novembre 2026

## Conclusion
Accord sur les calculs et la recommandation, après correction de deux formulations qui pouvaient changer la décision : le modèle fermé convient à un mélange réellement fermé, pas à un réservoir maintenu ; une obstruction stationnaire ne rejette pas automatiquement une approximation à court terme. La version finale de ASSESSMENT_FR.md intègre ces corrections et exige observable, norme, horizon et tolérance avant de poursuivre.

Aucune nouvelle preuve Lean dans ce jalon. Il s'agit d'analyse mathématique et de tests exacts d'équilibre, sans données biologiques, ajustement ni intégration numérique du système original.

## Reproduction indépendante
Source : math-bounds-lab/closed-binding-assessment.
Contrôle effectué sur copie indépendante ; sortie reproduite dans verification/independent-run-output.json.
Le script copié a été exécuté avec succès : PASS, 48 couples rationnels. Le JSON reproduit est identique octet pour octet à celui de l'auteur. SHA256 du script original et copié : 9c7b7b3b0bde3fad61cae837c35d0a762eac705b287447f10e46465524d43918.
Aucune source de l'auteur modifiée par le relecteur. Copie finale documentaire : ASSESSMENT_FINAL_FR.md ; journal : reproduced-tests.log.

## Analyse vérifiée
Hypothèses : réaction monosite bien mélangée, action de masse, Rtot>0, koff>0, kon≥0, μ=Ltot/Rtot≥0, α=kon Rtot/koff≥0. Le benchmark part de C(0)=0 et compare la solution fermée au ligand libre figé à Ltot. Un complexe initial non nul changerait cette convention ; les garanties ne se transfèrent pas sans analyse.

Pour F(z)=1−z−αz(μ−1+z), l'intervalle Iμ=[max(0,1−μ),1] est invariant : F à sa borne basse vaut min(μ,1), F(1)=−αμ. Sa dérivée satisfait F′≤−1−α|μ−1|. Continuité et stricte décroissance donnent un unique équilibre physique, y compris les cas α=0 ou μ=0.

Avec λ=1+αμ, d=z−y satisfait exactement d′=−λd+αz(1−z), d(0)=0. Le maximum de z(1−z) sur Iμ vaut q(μ)=μ(1−μ) pour μ≤1/2 et 1/4 sinon. Variation des constantes donne
0≤d(s)≤αq(μ)/λ · (1−exp(−λs)).
Cette borne est absolue, normalisée par Rtot, identique pour fractions libre et liée. Elle ne contrôle pas l'erreur relative au complexe ni celle des constantes inférées.

Le plafond simple B=α/[4(1+αμ)]≤1/(4μ) pour μ>0 justifie μ≥25 comme condition suffisante d'erreur absolue ≤0,01 pour tout temps. Ce n'est pas une condition nécessaire. Avec ε=α/[1+α(1+μ)], B=ε/[4(1−ε)] ; ε≤1/26 suffit. La notation Kd=koff/kon requiert kon>0 ; le cas kon=0 est correctement traité directement par ε=0.

Pour 0<μ<1, la violation stationnaire de capacité équivaut à α(1−μ)>1. L'exclusion μ=0 est indispensable et testée. L'absence de violation n'assure pas une bonne approximation.

## Exemple décisif et corrections de portée
Pour α=10, μ=1/10, équilibre fermé (4+√26)/10≈0,909902, ouvert 1/2, écart≈0,409902. Mais, sur 0≤s≤1/100, d(s)≤(9/20)(1−exp(−2s))≤(9/10)s≤9/1000<0,01. Rejeter ce modèle approché pour toute fenêtre aurait donc été faux. La trajectoire ouverte atteint la capacité minimale 9/10 à s_cap=log(5/4)/2≈0,111572, puis la viole. La note finale distingue bien court terme et équilibre.

Autres contrôles : α=1, μ=1 donne un écart stationnaire≈0,118034 ; α=1, μ=25 donne≈0,001475 sous plafond1/104 ; α=1, μ=0,001 donne≈0,000499 absolu mais≈99,85 % relativement au complexe ; α=2, μ=1 donne exactement1/6, égal au plafond simple. Cette dernière égalité montre que ce plafond ne peut être uniformément remplacé par une constante arbitrairement plus petite.

## Ce que prouvent les tests, et ce qu'ils ne prouvent pas
Fraction évite l'arrondi dans les assertions. La dichotomie encadre une racine avec F(lo)≥0≥F(hi) ; l'interprétation comme unique équilibre utilise continuité et monotonie vérifiées analytiquement. Les tests vérifient les bornes d'équilibre, le critère de capacité et plusieurs contrastes de normes sur 48 cas. Ils ne démontrent pas les énoncés paramétriques généraux et ne testent pas les trajectoires transitoires par un solveur indépendant. La borne transitoire est une démonstration analytique séparée, non un résultat expérimental ou certifié Lean. Les décimales servent seulement à présenter les encadrements rationnels.

## Littérature et limites
Les passages consultés de Du (2024), DOI10.1021/acs.jcim.4c00130, montrent un antécédent direct de comparaison exacte/PFO et d'ajustement de six mesures sans bruit issues de la solution exacte. Le résumé publié de Stroberg et Schnell, DOI10.1016/j.mbs.2016.09.010, confirme la distinction entre fidélité des courbes et estimation des constantes. La prépublication accessible sur miroir n'est pas une version finale garantie identique et son extraction dégrade certains symboles. Les équations et normalisations citées dans la note ne doivent pas être attribuées à une lecture intégrale vérifiée de la version éditée. La note documentaire annonce ces limites.

La reformulation de la solution quadratique dans SOURCES_FR.md est algébriquement cohérente pour α>0, μ>0 : ses deux racines, son taux exponentiel et sa condition initiale correspondent au champ fermé. Elle est connue, non une découverte. Aucun code de Binding Curve Viewer inspecté ou exécuté dans cette revue. Les résultats de publications biologiques ne valident pas les paramètres ni l'application du laboratoire présent.

## Décision
Ne pas poursuivre une grande formalisation uniquement pour produire un nouveau jalon. Choisir d'abord le système physique ouvert/fermé, puis observable, normalisation, horizon, tolérance et conditions initiales. Un futur contrôle à trois espèces et une étude d'inférence seraient des travaux distincts, non déjà réalisés par ces 48 tests.
