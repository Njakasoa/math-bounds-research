# SLAC/ABTS à 25 °C : faisabilité d'un benchmark conditionnel

## Verdict
Le jeu public permet une comparaison computationnelle et descriptive pertinente : huit conditions, trois trajectoires par condition et un modèle exporté explicitement spécifié. Il est particulièrement utile pour tester l'import, les conventions et les limites d'un certificat. En revanche, l'archive ne doit pas être simulée automatiquement comme un SBML standard en supposant que ses noms d'unités et ses signes sont cohérents.

Le replay ci-dessous concerne uniquement les équations de concentrations explicitement déclarées dans le notebook public. L'archive originale n'a pas été corrigée. Une reproduction de courbes sauvegardées est obtenue ; ce n'est ni une reproduction complète de l'estimation statistique, ni une validation biologique. Aucun modèle monosite des jalons précédents n'est substitué au modèle SLAC.

## Sources et observations
Source : Max Häussler, DaRUS-3867, version 1, https://doi.org/10.18419/DARUS-3867 ; fichier 25 °C https://doi.org/10.18419/DARUS-3867/12. SHA256 de slac25.omex : 6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3. La licence CC BY 4.0 et la date de publication 9 janvier 2024 sont reprises du relevé primaire fourni ; elles ne sont pas embarquées dans l'OMEX. Une publication finale évaluée par les pairs n'est pas établie dans cet audit.

Notebook lu comme JSON, jamais exécuté : https://raw.githubusercontent.com/EnzymeML/slac_modeling/main/slac_kinetics.ipynb, empreinte 14d2c07bfc6b07e10e3317bd3176f7b8b1479c0ebe015732b54627235c79e9a8. Le lien main est mutable : cette empreinte, et non l'URL seule, fixe la copie examinée.

L'OMEX contient 8 CSV sans en-tête, 11 temps communs irréguliers de 0 à 14,9833333 minutes nommées et 3 réplicats de puits : 264 valeurs positives finies d'ABTS s1. Ce ne sont pas 264 mesures indépendantes d'enzyme ou de produit. Les CSV sont des concentrations issues d'une calibration d'absorbance, même si l'annotation isCalculated=False ne le reflète pas. Les absorbances brutes et la calibration complète ne sont pas dans cette archive.

Les concentrations initiales nominales vont de 5 à 150 µM nommés. Les huit moyennes mesurées à t0 sont inférieures au nominal, de 2,19 % à 21,32 %. Elles sont conservées séparément. C6 est décalé vers le haut par rapport à A6/B6 à tous les instants ; aucun point n'a été supprimé ni déclaré statistiquement aberrant. Le notebook retire la condition nominale 200 µM avant l'export ; ce n'est pas une exclusion ajoutée par notre audit.

## Convention de signe et d'unités : obstacle d'import vérifié
Les définitions XML u1 à u5 ne correspondent pas littéralement à leurs noms : notamment « min » encode 600 secondes, « µmol/L » encode 0,1 µM et « K » encode 10 K selon les facteurs SBML. L'unité de volume µL est cohérente. Les tableaux d'audit conservent les deux lectures sans redimensionnement silencieux.

Les kineticLaw sont −S·E·k_cat/(K_M+S) et −k_ie·E, alors que les réactions sont déjà orientées vers la consommation de S et E. Un moteur appliquant normalement la stœchiométrie à ces flux négatifs inverserait leur effet. Les lois sont aussi de type concentration/temps, tandis qu'un flux réactionnel SBML standard est de type quantité/temps ; les conditions initiales des mesures sont dans les annotations EnzymeML. Nous n'avons pas exécuté un validateur SBML complet et ne prétendons pas à un verdict de conformité de schéma. Le constat est celui d'une ambiguïté de portabilité sémantique.

Le notebook lève l'ambiguïté pour son modèle de concentrations : il écrit explicitement substrate = −(substrate*catalyst*k_cat)/(K_M+substrate), catalyst = −k_ie*catalyst, avec minutes et µM. Notre interprétation conditionnelle est donc
S′=−k_cat E S/(K_M+S), E′=−k_ie E.
La température/pH documentés sont 25 °C et 3 ; ils ne sont pas des variables simulées ici. Les autres espèces déclarées ne constituent pas des observations supplémentaires. L'équation exportée n'identifie pas à elle seule tous les mécanismes chimiques possibles.

## Ajustement et incertitude : ce qui est établi
Paramètres exportés : k_cat=23,8113065508133 min⁻¹, K_M=22,9403691771082 µM, k_ie=0,0608219180888591 min⁻¹ ; E0 nominal=0,073938727 µM.

Le notebook ajuste d'abord k_cat et K_M sur les trois premières minutes, puis les maintient fixes pour estimer l'inactivation sur la série complète. L'export sélectionne la variante Michaelis–Menten avec inactivation par son nom. Ce n'est pas la variante au meilleur AIC parmi celles affichées à 25 °C : la sortie indique environ −398 pour cette variante contre −514 pour inhibition compétitive du produit avec inactivation. Nous ne remplaçons pas le modèle exporté par cet autre modèle et n'en déduisons aucune causalité mécanistique.

Les champs stdev et les bornes d'optimisation sont présents. Les bornes de l'optimiseur ne sont pas des intervalles de confiance. La signification exacte des stdev, leur mise à jour entre étapes, les corrélations et la pondération des résidus ne sont pas établies. Une tentative d'accès à la source de l'estimateur a été refusée ; elle a été arrêtée sans route alternative. Aucun écart-type n'a été transformé en borne certaine ou en intervalle de confiance improvisé.

Les triplicats permettent de décrire une dispersion, pas de reconstruire automatiquement l'incertitude de calibration, la dépendance entre puits, les erreurs systématiques ou l'incertitude de E0. L'enzyme active E(t) n'est pas observée directement ici ; un bon ajustement de S ne démontre pas que l'inactivation soit le mécanisme unique.

## Reproduction obtenue, puis comparaison descriptive aux mesures
Les huit courbes sauvegardées commencent à la moyenne des trois t0 mesurés. Cela établit la convention de visualisation, pas celle des résidus internes de l'estimateur.

L'équation possède une référence implicite monotone : E(t)=E0 exp(−k_ie t) et
S0−S(t)+K_M log(S0/S(t)) = (k_cat E0/k_ie)[1−exp(−k_ie t)].
Nous la résolvons indépendamment et la comparons à une intégration numérique DOP853. Écart maximal : environ 3,24×10⁻¹⁰ µM. La référence reproduit les 800 points des huit courbes sauvegardées à environ 1,96×10⁻⁷ µM près. Ces 800 points sont des prédictions archivées, pas des observations expérimentales supplémentaires. Ces accords numériques ne sont pas des certificats d'arrondi.

Avec initialisation par moyenne t0, la RMSE descriptive sur les 240 observations après t0 vaut environ 0,87974 µM. Avec les concentrations nominales comme initiales, elle vaut environ 2,47557 µM. Cette comparaison illustre l'importance du choix initial ; elle ne prouve pas la convention utilisée par l'estimateur. Les données ont déjà servi à l'ajustement des paramètres exportés : aucune validation hors échantillon n'est revendiquée. La RMSE n'est ni une probabilité de couverture, ni une certification du modèle.

## Test précis proposé pour le cadre mathématique
1. **Import avec refus explicite de l'ambiguïté.** Un import générique doit signaler les incompatibilités, pas modifier signes, unités ou initiales en silence. Le mode notebook-déclaré reste séparé de la lecture SBML littérale.
2. **Abstention correcte sur la contraction globale.** Pour E=0, le flot à tout temps positif et la transition Euler fixent chaque état (S,0). Une boîte contenant deux valeurs distinctes de S à E=0 ne peut donc avoir de contraction stricte globale. Accepter un tel certificat serait une erreur du checker. Le champ f(S,0)=0 exprime un équilibre ; nous ne confondons pas le champ avec sa transition.
3. **Garantie conditionnelle finie sur la réduction scalaire.** Aux paramètres ponctuels fixés, E(t) est prescrit par sa solution analytique. Pour 0≤S≤150 µM et 0≤t≤15 min, K_M+S≥K_M>0. Une étape scalaire utilisant E(t) exact est positive et non expansive si h≤K_M/(k_cat E0), ici environ 13,03 min. Ce seuil est une condition de stabilité/positivité, pas une recommandation de précision. Ce résultat ne prouve ni contraction du couple (S,E), ni propriété d'un Euler simultané sur ses deux équations.
4. **Budget de discrétisation préannoncé.** Choisir, pour le benchmark computationnel seulement, une cible de 0,01 µM aux nœuds de la grille sur un horizon de 15 minutes. C'est notre seuil de test, pas une tolérance expérimentale publiée. Poser V=k_cat E0 et C=V(k_ie+V/K_M). Sur une solution physique, 0≤S″≤C : le défaut local scalaire est au plus Ch²/2. La non-expansion propage alors l'erreur en au plus ChT/2, pour des pas au plus h et une même initiale. Avec h=1/200 min et T=15 min, le budget exact calculé en rationnels sur les décimales archivées vaut environ 0,00908245 µM, inférieur à 0,01. Le replay flottant observé donne un écart maximal d'environ 0,00227925 µM aux instants de mesure. L'évaluation flottante de exp et les arrondis du code ne sont pas certifiés par cette seule borne analytique. Une réalisation avec intervalles ou preuve formelle serait une étape ultérieure explicite, pas un résultat déjà livré. Cette majoration concerne les nœuds de la grille ; aucune erreur d'interpolation entre nœuds n'est établie.

La contraction scalaire stricte sur l'horizon observé peut également être bornée, mais elle est très faible sur toute la boîte : facteur environ 0,9999457 pour h=0,1 min. Cela ne justifie ni oubli rapide des initiales, ni convergence globale vers une cible unique quand E tend vers zéro.

## Faisabilité et limites restantes
Le benchmark est faisable pour l'audit d'import, le replay du modèle déclaré, un test d'abstention et un budget numérique conditionnel. Les données permettent une comparaison descriptive utile de S, avec réplicats et plusieurs conditions. Elles ne suffisent pas, à elles seules, à établir une enveloppe probabiliste complète, à valider l'inactivation, un effet conformationnel ou une généralité biologique.

Pour une comparaison expérimentale plus forte, il manque une sémantique vérifiée des résidus/stdev, la calibration avec ses incertitudes, le traitement de l'initialisation, et un plan de validation indépendant. Un partage par séries/conditions entières serait un ajout méthodologique à annoncer, pas une pratique à attribuer aux auteurs. Aucun nouvel ajustement n'a été effectué ici. Aucune expérience physique, manipulation d'organisme ou extrapolation d'un autre modèle n'est proposée.
