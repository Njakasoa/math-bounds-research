# Reproduction du benchmark réactionnel

Outils requis : binaire Linux officiel Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 et ses dépendances/caches épinglés. Les identifiants sont dans verification/environment.json et mathlib-lake-manifest.json. Aucune installation ni requête réseau n'est faite par le script.

Définir LEAN_BIN et MATHLIB_DIR comme chemins absolus, puis lancer ./rebuild.sh. Le script vérifie l'empreinte/version du binaire et le commit Mathlib, reconstruit les 6 modules dans build/ avec un chemin d'import isolé, puis exécute AuditReaction.lean. Les objets Mathlib sont réutilisés et non recompilés intégralement.

python verify_outputs.py contrôle 40 déclarations nommées du nouveau code et les six sondes du checker : true,false,false,true,true,true. Seuls propext, Classical.choice et Quot.sound sont admis par cet audit ; le contrôle de texte ne remplace pas le noyau Lean.

python experiments/check_binding.py exécute les assertions discrètes en Fraction exactes, et régénère binding-results.json. Seule l'exponentielle illustrative est calculée en virgule flottante ; les décimales affichées ne sont pas des preuves. Python utilise sa bibliothèque standard.

Vérifier les fichiers distribués par sha256sum -c SHA256SUMS, généré lors du conditionnement final. Le répertoire build/ n'est pas distribué. Les trois imports historiques sont inchangés : BernsteinCertificate, GlobalScalarMap et TrackingRecurrence, provenant des jalons publiés du dépôt https://github.com/Njakasoa/math-bounds-research au commit fc75b64e5f4658a849595de45bd98db657474308.

Portée formelle : conservation des deux flux et réduction algébrique ; condition initiale, dérivée et invariance de la formule analytique à entrée constante ; invariance/monotonie Euler, garde rationnelle et certificats ; invariance des trajectoires admissibles et borne de suivi discrète. Aucune borne d'erreur globale Euler–ODE ni preuve d'adéquation empirique n'est incluse.
