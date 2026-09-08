# Diagnostic privé — frais, arithmétique et gaz EIP-8282

Date d'exécution : 2026-09-08. Chaque énoncé factuel porte une étiquette :
`[testé]`, `[éprouvé]`, `[hypothèse]` ou `[ouvert]`.

## Portée et versions

- `[testé]` Le dépôt `lfglabs-dev/eip-8282-proof-closure` est exécuté depuis le commit de base `f14791d482690c64b71c17f63024d78459d15939`, sur la branche privée `private/direct-fees-diagnostics`.
- `[testé]` `lake-manifest.json` fixe EVMYulLean à `b62586650b4f96cc6da25f36574aaa8f329a6420`; aucun fichier de cette dépendance n'est modifié.
- `[testé]` L'interpréteur employé est directement `EvmYul.EVM.Ξ`, via le pilote existant `Eip8282.Audit.EvmRunner`; le modèle abstrait n'intervient pas dans les résultats ci-dessous.
- `[testé]` EVMYulLean déclare `TargetSchedule := "Cancun"`, tandis que les sources assembleur épinglées déclarent `#pragma target "prague"`.
- `[hypothèse]` Pour les opcodes parcourus par ces traces (`PUSH0`, stockage, branchements, arithmétique, mémoire, log et retour), la sémantique Cancun de l'interpréteur coïncide avec celle attendue à Prague.
- `[ouvert]` Ces essais ne constituent donc pas une validation complète du bloc Prague ni des règles de création/invocation propres au protocole EIP-8282.

## Images épinglées et constructeurs

- `[testé]` Dépôts, constructeur : 638 octets, SHA-256 `166510c29d9ea96c80b854e86743377de1cadccaef62a620c684641fb9267f61`.
- `[testé]` Dépôts, runtime : 628 octets, SHA-256 `2c49dcf745b1304f3dac0ea7487eae6d8fd07812ada980d542f79e8e5e53eb8d`.
- `[testé]` Sorties, constructeur : 503 octets, SHA-256 `37d89175964e696bfed69ad5309c0147bdb7af8b11a25ea1ba557d7adb9d50b8`.
- `[testé]` Sorties, runtime : 458 octets, SHA-256 `c889ed88730d157d192aae28c2dee61324d0df3bd01ff0078386808b4adb27aa`.
- `[testé]` L'exécution diagnostique du constructeur des dépôts avec 30 000 000 de gaz réussit, consomme 136 gaz, retourne exactement les 628 octets du runtime et laisse le slot 0 à zéro.
- `[testé]` L'exécution diagnostique du constructeur des sorties avec 30 000 000 de gaz réussit, consomme 22 211 gaz, retourne exactement les 458 octets du runtime et laisse le slot 0 à `2^256-1`.
- `[ouvert]` Le pilote appelle le code d'initialisation par `Ξ`; il ne modélise pas l'enveloppe `CREATE`, l'adresse réservée ni l'installation du compte par une transition de fork. Les deux observations précédentes portent donc sur le code d'initialisation, pas sur un déploiement protocolaire complet.

## État initial et séquence exacte

- `[testé]` Chaque ligne de `evm.txt` est une exécution indépendante sur un monde frais; aucune ligne ne réutilise le post-état de la précédente.
- `[testé]` Le compte cible commence avec un solde nul, le runtime épinglé et les slots indiqués; le compte appelant contient exactement `msg.value + 10^18` wei.
- `[testé]` Les appels constructeur utilisent l'appelant `0x1234`, valeur zéro, calldata vide, stockage vide, fuel 200 000 et gaz 30 000 000.
- `[testé]` Les appels de frais utilisent l'appelant non-SYSTEM `0x1234`, valeur et taille de calldata indiquées dans `evm.txt`, slots `(excess,count,head,tail) = (X,0,0,0)`, gaz 30 000 000 et fuel 200 000, sauf `X=2893` où le fuel vaut 300 000.
- `[testé]` La séquence reproductible est : calcul indépendant et hachage des quatre images; compilation de la FFI et du pilote; deux exécutions du code constructeur; getters sorties à 1608 et 1620; soumissions sorties à `fee-1` puis `fee`; getter sortie à 2893; getter dépôt à 2893.
- `[testé]` Aucun appel de cette séquence n'usurpe `SYSTEM_ADDRESS`; toutes les adresses source valent `0x1234`.
- `[testé]` Les deux soumissions à 1620 portent une pubkey de 48 octets nuls; l'expérience teste la frontière d'acceptation de la couche exécution, pas l'autorisation ou l'application consensus de cette demande.
- `[testé]` Les scénarios de frais injectent directement les slots de stockage, notamment 1608, 1620 et 2893.
- `[ouvert]` Ces stockages injectés ne démontrent ni leur accessibilité par une suite de blocs valides ni la possibilité économique de cette suite.
- `[ouvert]` Aucune conclusion de protocole ne doit être tirée de l'ordre des lignes, puisque les exécutions sont isolées et non une chaîne de blocs.

## Boucle complète contre mots de 256 bits

- `[testé]` L'oracle indépendant applique la récurrence `output += accumulator; accumulator = (X * accumulator) / (iteration * 17); iteration += 1`, soit sur entiers non bornés, soit avec réduction modulo `2^256` après chaque opération EVM.
- `[testé]` À `X=1608`, les deux arithmétiques terminent après 257 itérations et donnent le même frais `119989470856188333158662703311252429458084` wei.
- `[testé]` Le getter du runtime sorties à `X=1608` retourne exactement ce mot et consomme 26 781 gaz.
- `[testé]` Cette trace réfute toute borne universelle de 256 itérations pour cette boucle sur stockage arbitrairement injecté.
- `[ouvert]` Elle ne réfute pas une borne portant uniquement sur des états prouvés accessibles par des blocs valides.
- `[testé]` À `X=1620`, les deux arithmétiques terminent après 258 itérations et donnent le même frais `243056981773394081136356734028591621772929` wei.
- `[testé]` Le getter du runtime sorties à `X=1620` retourne exactement ce mot et consomme 26 868 gaz.
- `[testé]` Avec 48 octets nuls et `msg.value = 243056981773394081136356734028591621772928`, soit exactement un wei de moins, le runtime sorties revert après 26 849 gaz.
- `[testé]` Avec les mêmes données et `msg.value = 243056981773394081136356734028591621772929`, le runtime sorties réussit et consomme 96 582 gaz.
- `[testé]` À `X=2893`, la première différence intermédiaire apparaît à l'itération 167 : le produit entier vaut `116599123967514564445820046889913593626799365321332351753526139120293263618495`, supérieur à `2^256-1`.
- `[testé]` À cette itération, le produit EVM réduit vaut `807034730198369022249061881225685773529380655691787714068555112380133978559`; l'accumulateur suivant vaut `284267252623588947604459979297529331993441583547653298368635122360033102`, contre `41070491006521509139070111620258398600492907827168845281270214554523868833` en entiers complets.
- `[testé]` À `X=2893`, la boucle entière termine en 462 itérations avec le frais `80668064690921409049190791237320678716946849613533250306370202067869504081`, tandis que la boucle EVM termine en 457 itérations avec le frais `32087365885911168062721653499988857431024628719292649881555161070975172167`.
- `[testé]` Les runtimes sorties et dépôts retournent tous deux exactement le frais EVM précédent à `X=2893` et consomment chacun 44 181 gaz.
- `[éprouvé]` Aucun nouveau théorème Lean n'est revendiqué dans cette branche; tous les nombres ci-dessus sont des observations testées.

## Gaz et limites de l'observation

- `[testé]` Tous les appels disposent initialement de 30 000 000 de gaz, valeur dédiée annoncée par le texte EIP pour l'appel système, même si les appels de frais de cette expérience sont des appels utilisateur.
- `[testé]` Entre 1608 et 1620, une itération supplémentaire augmente le gaz du getter de 87, de 26 781 à 26 868.
- `[testé]` Le getter à 2893 reste très inférieur à 30 000 000 de gaz dans cet interpréteur, avec 44 181 gaz consommés.
- `[ouvert]` Ces mesures ne prouvent pas une borne générale de gaz, car aucune terminaison universelle ni borne d'accessibilité sur `excess` n'est établie ici.
- `[ouvert]` Le fuel Lean est un budget d'interprétation distinct du gaz EVM; le succès observé ne permet pas de les identifier.

## Barrières économiques et obligations de préservation

- `[testé]` Le frais observé à 1608 vaut environ `1.20 × 10^41` wei et celui à 1620 environ `2.43 × 10^41` wei; la soumission exacte à 1620 n'est possible dans le harnais que parce que le solde artificiel de l'appelant est initialisé à `msg.value + 10^18`.
- `[hypothèse]` Dans un état économique réel, l'exigence de paiement, le verrouillage du frais, le principal minimal d'un dépôt et l'augmentation du frais constituent des barrières fortes à l'accumulation de demandes nécessaire pour produire de tels excès.
- `[ouvert]` L'ampleur exacte de ces barrières dépend de la trajectoire de blocs, de l'offre et de la distribution des soldes, des remboursements absents, des top-ups et des règles consensus; ce rapport ne démontre pas l'inaccessibilité de 1608, 1620 ou 2893.
- `[hypothèse]` Toute garantie économique doit préserver au minimum : conservation des soldes, transfert exact de `msg.value`, frais et surpaiement verrouillés, principal des dépôts, incrément de `count` seulement après succès, drain plafonné, mise à jour système d'`excess`, inhibition et validité consensus des demandes.
- `[ouvert]` Il ne serait pas fidèle de remplacer ces obligations par `msg.value ≤ 10^30` ou par une hypothèse globale `noWrap`; aucune de ces hypothèses n'est adoptée ici.

## Lemmes EVM-directes proposées, sans cycle

- `[hypothèse]` Niveau 1 — `fee_block_decodes_pin` : décodage du bloc d'instructions de la boucle depuis l'image runtime explicite; dépend uniquement des octets épinglés et des définitions EVMYulLean.
- `[hypothèse]` Niveau 2 — `fee_iteration_word_exact` : une itération de `Ξ` réalise exactement les opérations `UInt256` du bytecode, y compris les réductions; dépend seulement du niveau 1 et des règles locales d'opcode.
- `[hypothèse]` Niveau 3 — `fee_loop_reaches_exit_of_word_witness` : un témoin fini de la récurrence mot mène au bloc de sortie avec coût `87*n + c`; dépend seulement du niveau 2 et d'une composition de reachability.
- `[hypothèse]` Niveau 4 — `getter_returns_fee_word` et `submission_fee_boundary` : le getter retourne `output/17`, et les valeurs `fee-1`/`fee` choisissent respectivement revert/succès; dépendent seulement du niveau 3 et des blocs terminaux décodés.
- `[hypothèse]` Niveau 5 — `system_preserves_economic_state_relation` : une transition système authentique relie comptes, file, `count` et `excess`; dépend des chemins système EVM-directs, sans dépendre des niveaux utilisateur 3–4.
- `[hypothèse]` Niveau 6 — une correspondance économique ou abstraite peut consommer les niveaux 4 et 5; elle ne doit pas être importée en retour par les lemmes EVM-directs.
- `[ouvert]` Une preuve de terminaison universelle sur mots, une borne de gaz sur états protocolaires et une caractérisation d'accessibilité économique restent à construire.
- `[ouvert]` La correspondance globale `Ξ ↔ Model` n'est pas un préalable aux niveaux 1–5; le modèle abstrait reste auxiliaire.

## Reproduction

- `[testé]` `LEAN_LAKE=/chemin/vers/le/lake-du-toolchain-4.31.0 bash scripts/direct-fees-run.sh` régénère `arithmetic.json` et `evm.txt` après compilation de la FFI et du pilote.
- `[testé]` `arithmetic.json` contient les résultats entiers et mots ainsi que toutes les opérations intermédiaires qui franchissent `2^256`; `evm.txt` contient les statuts, sorties et consommations de gaz observés.
