# Reproduction du paquet d'atlas certifié

Lire `RESULTAT_FORMEL_FR.md` pour les énoncés et les limites.

## Environnement exact

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- SHA256 du compilateur : `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib : `d13f23b723b8a846827a245b89c10fc7d3f11612`, avec ses dépendances épinglées et objets officiels.

Aucun accès à Azurite n'est nécessaire pour ce périmètre. Le compilateur et les caches ne sont pas inclus dans cette archive.

La release officielle est https://github.com/leanprover/lean4/releases/tag/v4.34.1 . L'archive Linux x86_64 `lean-4.34.1-linux.tar.zst`, annoncée à 554 Mo, a pour SHA256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`. Les empreintes d'archive et de binaire sont distinctes et ont été vérifiées.

Pour Mathlib, la méthode officielle de récupération des objets est `lake exe cache get` au commit épinglé. La variable officielle `MATHLIB_CACHE_DIR` permet de choisir un cache dans un dossier autorisé. Cette récupération télécharge des dépendances ; le script de reconstruction livré, lui, ne télécharge rien.

## Reconstruire

Vérifier les fichiers avant reconstruction :

```sh
sha256sum -c SHA256SUMS
```

Configurer les chemins vers l'environnement déjà préparé puis exécuter :

```sh
export LEAN_BIN=/chemin/lean-4.34.1-linux/bin/lean
export MATHLIB_DIR=/chemin/mathlib
bash rebuild.sh
```

Le script vérifie les versions et empreintes, reconstruit les 25 modules dans `build/`, puis relance l'audit des 104 déclarations et les trois sondes du checker. Les objets de production du lab ne sont pas utilisés : seuls les objets du nouveau dossier et les dépendances Mathlib sont dans les chemins d'import. Les modules sont compilés avec `-j2`.

Les journaux de cette reconstruction se trouvent dans `verification/rebuild/`. Les essais de développement et les premières erreurs de coercition ne sont pas des validations ; les journaux finaux livrés correspondent aux sources finales.

## Rejouer les sondes du checker

Après reconstruction, sous le même `LEAN_PATH`, `RuntimeProbes.lean` évalue le checker sur l'exemple et retourne `true`, une amplitude `4/3` et une borne Lipschitz `1/4`. Les sondes exécutables ne remplacent pas les théorèmes de correction et d'existence.

## Périmètre

Le résultat général concerne une grille uniforme finie avec multiplicateurs constants. Les exemples à deux cellules emploient des multiplicateurs quadratiques. La preuve générale est classique et non calculatoire ; aucun algorithme extrait ni temps pratique garanti n'est livré.

## Tests rationnels complémentaires

`python3 experiments/check_atlas.py` rejoue les certificats rationnels, leurs contrôles indépendants SymPy, quatre corruptions volontairement rejetées et les tests de dimensions et de frontières. Les versions Python/SymPy utilisées sont enregistrées dans `verification/python-environment.json`. Ce programme est un générateur de cellules de son format, pas un validateur général d'entrées externes. Il est séparé de la formalisation Lean et n'en constitue pas une extraction.
