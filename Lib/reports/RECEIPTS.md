# Provenance receipts (item 2)

Coverage: every baseline commit of lanes A, D1, D2, H, I, B (the ones
without an inline SHA-256) plus the eleven lane-A files that arrived inside
`44c11ef`. Ranges are cut at declaration boundaries so the hashes reproduce.
Renaming families resolved by the recorded lane renames (`CuspRetraction.Patching` -> `LocalCollapse`,
`ThreefoldHomologyFinitenessRetraction` -> `SublevelRetraction`, `CoveringOrthant` -> `CoveringChart`,
`FirstHurewicz` -> `SingularChains`). Known anonymous-instance exception:
`Suspension.instLocal1` (auto-generated name). Kimi-lane target files
(Hurewicz/*, LinearAlgebra/*, Algebra/Group/*) are excluded here; their
receipts belong to the C/J owners. Full data: `RECEIPTS_DATA.json`.

Reproduce a row: `git show 721fc82:FILE | sed -n "A,Bp" | sha256sum`.
Verified: 8/8 random sample rows reproduce (2026-09-12).

| 721fc82 source range | SHA-256 | target file | decls | baseline commit |
|---|---|---|---|---|
| `Hopf/DifferentialTopology.lean:30922-31137` | `192d0e034322e7dae66aba63c7db88a86e0a5ed93978c7e7329ec8c51c0a7bdb` | `Lib/Algebra/Homology/MayerVietorisShortExact.lean` | 19 | bd7a4b5 A |
| `Hopf/SingularHomology.lean:85-672` | `2c034cbfcfbf9f19d252f0da8b3950f57ca27787655c6bbfeabc0a5c4a944909` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 87 | cd31909 A |
| `Hopf/SingularHomology.lean:677-684` | `65075020184a932dd7532227d18a53a66c2a1fbc1a6cfdc72f31794674c8af2c` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 1 | cd31909 A |
| `Hopf/SingularHomology.lean:692-694` | `55b8d11f74ca24d9799185dc2e70093bcd8d0e74ee29014444be25bdb6d0e21e` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 1 | cd31909 A |
| `Hopf/SingularHomology.lean:738-868` | `97373a55dd13d1f634a7f7587604983e28cc3759f88002e235ef01b1cd1eba36` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 18 | cd31909 A |
| `Hopf/SingularHomology.lean:1018-1095` | `4f048241afbb528440f31162a3ffcd143ebb013060735e3185d58b58ed0d6a76` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 14 | cd31909 A |
| `Hopf/SphereTopology.lean:7020-7242` | `23b351114a6c8b22a9b7ba7fac5c94a1538747c3ac1bbe9547e1fba5cd511dc7` | `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | 32 | cd31909 A |
| `Hopf/SingularHomology.lean:3659-3834` | `f81dab85d2ab018645585213bce74a84fe696742f3fbeb69c518e9d16737e54c` | `Lib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` | 24 | e997d6c A |
| `Hopf/SingularHomology.lean:4016-4040` | `b4044e66696cb07060fcb8a8ef256713a810be8037965591c308c658b4babdcd` | `Lib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` | 2 | e997d6c A |
| `Hopf/SingularHomology.lean:869-1017` | `a9f13c1a1a948473e57762bb339545d9b248511299eaec9ee572e744907f082f` | `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` | 16 | 81c066b A |
| `Hopf/SingularHomology.lean:1096-1860` | `e36a0f546e925a0016c45af25ba3c121f239c78542281536981eab787a5b1544` | `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` | 87 | 81c066b A |
| `Hopf/SingularHomology.lean:2088-3658` | `53fd13336e46e24a5f75e3ef02b298793d36bfe08444bcd43e930576a39f7284` | `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` | 146 | 81c066b A |
| `Hopf/SingularHomology.lean:1861-2087` | `fe28a16a8bf23db706b76f8e32d508177ed0d99c734c7f832821c07753dfaef7` | `Lib/AlgebraicTopology/SingularHomology/ModuleHomology.lean` | 20 | 90685ed A |
| `Hopf/Hurewicz.lean:545-676` | `a6126c0b67a41763229b66218ee36d8b370d312d60c61ece1ba301a121cc14a2` | `Lib/AlgebraicTopology/FundamentalGroup/SimplyConnectedCover.lean` | 9 | da29618 B |
| `Hopf/Hurewicz.lean:1065-1261` | `e812cd98ceda5ddb2341c1c82086b8f393285adcad739ccacfb0e79219ded5b9` | `Lib/AlgebraicTopology/FundamentalGroup/TwoSimplyConnectedCover.lean` | 19 | 0b5d47f B |
| `Hopf/LCP/BoundaryTopology.lean:8622-8767` | `e9d1ff3c3b8cc32559e87c7964425ce15893e11e5d182fafe014e77a40f4feec` | `Lib/AlgebraicTopology/FundamentalGroup/TwoSimplyConnectedCover.lean` | 10 | 0b5d47f B |
| `Hopf/Hurewicz.lean:719-1064` | `d022e6b360b1fc485f632f939db132fd0fe64eed8ba75b0e47c2d7e0f75cae88` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | 50 | eca3d71 B |
| `Hopf/Hurewicz.lean:1262-1325` | `01451ffaa598f43c0194c152d2c0e8ba176b34dac21cde77cf090dff5e7161ec` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | 1 | eca3d71 B |
| `Hopf/LCP/BoundaryTopology.lean:539-1675` | `8a2aabe771b94f4e2a685ca240a4865980142d6d9d9134f0e178ee20cd0b58e9` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | 111 | eca3d71 B |
| `Hopf/LCP/BoundaryTopology.lean:12954-12978` | `5487e3b5484874ed1e97ec18923f3dfcde21e571b0324f37e3be02e17681052b` | `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` | 1 | eca3d71 B |
| `Hopf/SingularHomology.lean:18734-18867` | `5ae3a7c573ddfeb3fcf0f412add99c6478a21c4e7c75f936f561bd1184465d9f` | `Lib/Topology/Homotopy/LoopSubdivision.lean` | 8 | f09e304 B |
| `Hopf/SphereTopology.lean:1481-2508` | `5ff9ac1b1af1bf997854ff9f8ff0f48bbc7d42406f5ccf9c54af30d0f5c8a4cb` | `Lib/AlgebraicTopology/SingularHomology/CircleProduct.lean` | 118 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:15326-15575` | `e68de4dd6859d542a8caf2a39029bdfdf02c28c169b5a05117f2cf1edac500c7` | `Lib/AlgebraicTopology/SingularHomology/Coproduct.lean` | 22 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:15589-15705` | `ff4d2c0241dc6ba8784e162dab9f828f7c878fcf75d60fbe6f9f4bbee1a98f7a` | `Lib/AlgebraicTopology/SingularHomology/Coproduct.lean` | 7 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:15706-15840` | `224eb59865bd67631227aac9e9670f77aa87f2976b53bca1ea7039b08c9c1b0f` | `Lib/AlgebraicTopology/SingularHomology/LocalContributions.lean` | 13 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:3835-4015` | `dae34e4841b5d62909ae06c86be9ecd6a38980f7dc63dac60477094dcba0b386` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 11 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:4041-4153` | `932e91b7407529b7e2eb5596e21b62990c76e4d2437ff62ece06c44cdf0556ec` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 5 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:4161-4170` | `a5632d8756bdb7a766d97999aeaf817b683b12549b2e7d8162403117f4f1f518` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 2 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:4218-4224` | `02b38cbe0674b1f24ad3a1d7984d8c586fd5fb509e25dcc19710b52cbca0c0f5` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 1 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:4297-4358` | `91d3abb540cf3042910d86211ef4d2f9c516db115a06bf4b8843ea16c6d4edd8` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 6 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:30894-30897` | `504420e0d396cc3ac16212658706510495544adc80e377c16dba6021073bfe73` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 1 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:31011-31013` | `bec7a8e8775f18f884f1ba066944a6d17bf0f45263aa89ececd5637a4dcecf8a` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 1 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:31021-31025` | `a19464488c5172cd01721c9426063d3f310a34ffeda1e8b0dbd1cc8b1a214b67` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 1 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:31034-31060` | `da1ea995148280748a951f816a932662d018bd57033e230e3393db46593c1b0d` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 3 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:31087-31260` | `74411b5b041fac6e7c88634b6227c3e297cbf869d2c397d751905ddbb6c4e9c5` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 15 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:31267-31274` | `c3089a7963e1a3cfc1c9d1043bae185ab0c649f40ec44284120bdc8817d73079` | `Lib/AlgebraicTopology/SingularHomology/LocalDegree.lean` | 1 | 44c11ef D1 |
| `Hopf/LCP/CuspFilling.lean:15076-15346` | `62191b7e3299c9d62f6d72cccf76a94c1299edb4d5608e7d6c0ffe74cddb14d3` | `Lib/AlgebraicTopology/SingularHomology/Naturality.lean` | 18 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:13759-13962` | `a96b70736751fd97e911f7406c8a66ccc350ac75e55b57685653ce40455b7834` | `Lib/AlgebraicTopology/SingularHomology/Naturality.lean` | 15 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:16386-16529` | `5417addb81a0d78b6b3472c4205a1ab92f574e454ae3ce3e0549d963c0ec4722` | `Lib/AlgebraicTopology/SingularHomology/Naturality.lean` | 13 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:17342-17373` | `504c2b664aac5277940f8298960435e47d65b0de1002ad1251d33d7af3c978d5` | `Lib/AlgebraicTopology/SingularHomology/Naturality.lean` | 2 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:85-329` | `3702da86f1a50ea29e08cfae5289a8d2cf70e6359f73f5c2a120c98c841af618` | `Lib/AlgebraicTopology/SingularHomology/Sphere.lean` | 37 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:2509-2562` | `3e45af0c3a1404f61c98ddc2e8d0f22052327ecc59b23d8b0043ed3364f8bf6b` | `Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` | 11 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:6863-6900` | `e79660ac8d91c5f9786f7fca2950c898b9f33960b94f323654c4fe305bd7e3e5` | `Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` | 5 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:16075-16146` | `0b57e0f47a8765a8d727ab3d4240051c3fda075e190fade7007f883f78b67dec` | `Lib/AlgebraicTopology/SingularHomology/SphereHomology.lean` | 6 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:1141-1480` | `3b359f079e27a7510c6121b29d36fae5935883e8b27bc8b862084d93d704a510` | `Lib/AlgebraicTopology/SingularHomology/Sum.lean` | 28 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:825-1140` | `f6c268e56522c8248d00d77f619d2ee9c092c3b885cb4bdb05dbddef88a315af` | `Lib/AlgebraicTopology/SingularHomology/Suspension.lean` | 33 | 44c11ef D1 |
| `Hopf/DifferentialTopology.lean:777-2989` | `00a0b304c27013e818527b90564ac7c1edf64e79e991eb39ea4ae8a7f0b33771` | `Lib/Analysis/Calculus/MorseLemma.lean` | 157 | 913716d D1 |
| `Hopf/DifferentialTopology.lean:18259-19185` | `60ad51e78504e427487a8d342d5c451f0a3edfbc78464fa7e47cd745cac1ce38` | `Lib/Analysis/ODE/SmoothFlow.lean` | 54 | 913716d D1 |
| `Hopf/Recognition.lean:1613-1640` | `f9c732eb9dd0f200b4319b842603668ad4dcd07318ac7f19e41b28070109c8c9` | `Lib/Geometry/Manifold/ChartedSpace/Transport.lean` | 3 | 44c11ef D1 |
| `Hopf/DifferentialTopology.lean:2990-3543` | `8db444fd9cf02056a5462a2cd4b36091317375059118ddb6b6f9601bef741b9c` | `Lib/Geometry/Manifold/Flow/Compact.lean` | 28 | 913716d D1 |
| `Hopf/DifferentialTopology.lean:5337-6989` | `f2af90454c7f0e9ce1b72f144eb07a3a9c83ec4f23e581bac831e1915220bfd3` | `Lib/Geometry/Manifold/Flow/HeightTranslating.lean` | 106 | 913716d D1 |
| `Hopf/DifferentialTopology.lean:6990-9042` | `ebe8c66c18470d999b538d0f7ef7319b06d27309bd4f5058233eef78013d9023` | `Lib/Geometry/Manifold/Morse/Existence.lean` | 117 | 913716d D1 |
| `Hopf/DifferentialTopology.lean:85-776` | `1ec365c49f7a0945f0fca692e92a2ce35ea68963c88040e6e7cd3b7058b2536e` | `Lib/Geometry/Manifold/Morse/Handle.lean` | 78 | 913716d D1 |
| `Hopf/DifferentialTopology.lean:3867-5336` | `c2b706bf7c7bc84bfe3e1f90f3597cf6490ce70fb9e53730072449b322e1c8ee` | `Lib/Geometry/Manifold/Morse/HandleAttachment.lean` | 125 | 913716d D1 |
| `Hopf/SphereTopology.lean:8246-8398` | `e916565c89e6460008cc0463069d7a54d9ce6eaf755c7d02ba75bb1857ac7f2d` | `Lib/Geometry/Manifold/Morse/Index.lean` | 16 | de4b876 D1 |
| `Hopf/SphereTopology.lean:8444-8474` | `39ff9752720d8747708017f2d0b25c342283c0f3afbef57a640e24f91ad6df7a` | `Lib/Geometry/Manifold/Morse/Index.lean` | 2 | de4b876 D1 |
| `Hopf/SphereTopology.lean:8592-8699` | `198b2d2eb08a2e34dc4fae350499906768ca7f8d5f8078cc65eb44536159eaf3` | `Lib/Geometry/Manifold/Morse/Index.lean` | 8 | de4b876 D1 |
| `Hopf/SphereTopology.lean:2595-2601` | `52e5343b859e3e5760fd6136871067a12dd883270140d4d458de9c2e722b0064` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 2 | de4b876 D1 |
| `Hopf/SphereTopology.lean:2606-2615` | `e5c35b201ea1f4560393feca9e30af3548521a2c5c0c2222645609d3ecfbd19b` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 1 | de4b876 D1 |
| `Hopf/SphereTopology.lean:2621-2647` | `3b8ab99fe2bd776c3e33e5ee11aef820d9c91d922ac09814f5773cbe41d996cf` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 4 | de4b876 D1 |
| `Hopf/SphereTopology.lean:7414-7439` | `addac04233dc939d38a1c30d0bfc20c027606d80a920e49558608fe8eec6e4fd` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 1 | de4b876 D1 |
| `Hopf/SphereTopology.lean:7677-7737` | `a9a2624f90e7cecb246d5fec3c2d3b688580a4ac5275b626a5a44940724a0b9e` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 3 | de4b876 D1 |
| `Hopf/SphereTopology.lean:7800-7818` | `a5bf3bcc191a77f9076247629adab20d5254fb0c1ae972aadc24c8cd6db4c911` | `Lib/Geometry/Manifold/Morse/SublevelSets.lean` | 1 | de4b876 D1 |
| `Hopf/DifferentialTopology.lean:3544-3866` | `a3025e150f48ad718ebe9d8d0ef66f7fc8a0a02842998806ecceb9420b42061e` | `Lib/Geometry/Manifold/RegularLevel.lean` | 20 | 913716d D1 |
| `Hopf/Recognition.lean:2090-2333` | `d446a33a128d5666f166cf5df71819a131c2483dd39f00a999174a4d422429f0` | `Lib/Topology/Homotopy/CylinderHEP.lean` | 23 | 44c11ef D1 |
| `Hopf/Recognition.lean:3197-3453` | `7e2159b612d39b412cd60ccc94698bfa07e5ad9d9d686fa3e39ddf2b1afbc0ba` | `Lib/Topology/Homotopy/CylinderHEP.lean` | 17 | 44c11ef D1 |
| `Hopf/SingularHomology.lean:5310-5858` | `c9d75ebcd40d9decc2cfcd2469df9267e50bff3410b6b2dbb5018f8473187091` | `Lib/Topology/Homotopy/HandleRetraction.lean` | 68 | 720a5ae D1 |
| `Hopf/SphereTopology.lean:330-351` | `48361756855fcaf87a4bbea9d7d6fcfacf5aec8f3b3e96694b3a966a766214f2` | `Lib/Topology/Homotopy/Suspension.lean` | 2 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:356-824` | `6f989fcc39d2146e0b0d68128825c2b8333bce61ff45705098c70c4c708229b4` | `Lib/Topology/Homotopy/Suspension.lean` | 63 | 44c11ef D1 |
| `Hopf/SphereTopology.lean:13388-13480` | `16e4cb16cd986865c5d8279563c75559150747a5b3f340b511e2db32a57df37e` | `Lib/Topology/OnePointCollapse.lean` | 12 | 44c11ef D1 |
| `Hopf/DifferentialTopology.lean:11602-13901` | `f11da1e7688a638f7a3228795905801a2e39a98aaa5b4d1d0600e21480f9d359` | `Lib/Geometry/Manifold/Collar.lean` | 147 | 488c283 D2 |
| `Hopf/DifferentialTopology.lean:23749-27461` | `20888bb712bd6a5ac513421732ae30d3bd33dbc4fe3bc5b81f5b01fc1f148e83` | `Lib/Geometry/Manifold/Immersion/Relative.lean` | 166 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:27473-27612` | `6a9b9adb61238b24233ba434ac214599a21b2926cf4a15c594e6c651ab388e3b` | `Lib/Geometry/Manifold/Immersion/Relative.lean` | 12 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:27620-28343` | `67d9a3b495c84191d018d27d5ebfee6d571b6e73cf33b4f64b68ec07b834cd54` | `Lib/Geometry/Manifold/Immersion/Relative.lean` | 35 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:14131-14999` | `697b416785fd8f46d0f4025b0765b0126b3a268d651c31a616d4d4c7714ad954` | `Lib/Geometry/Manifold/Morse/Cancellation.lean` | 33 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:15011-17991` | `b682d8ae12b5595eddf47ccb93b4b4cf95b97788591ff62ebbd401d7e3063542` | `Lib/Geometry/Manifold/Morse/Cancellation.lean` | 195 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:18082-18258` | `ab376c5e6ffae484c3b31a50c5abb13a403be4fc845177d603aa6806fa336ee0` | `Lib/Geometry/Manifold/Morse/Cancellation.lean` | 5 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:19186-19913` | `aa6f242801f08c88aff66497c09bd9694c0a1e68cfe8b311b0ac29bdfe2f65bf` | `Lib/Geometry/Manifold/Morse/Cancellation.lean` | 25 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:19923-20995` | `41f4648555d95830728d65d7d65472fb743e3b2dbf83fb656d1312a8de9cb825` | `Lib/Geometry/Manifold/Morse/Cancellation.lean` | 43 | 753ecf8 D2 |
| `Hopf/Recognition.lean:2580-3162` | `38c2f8982d3ede50634b00d5eee476251800c31112be063e6f0d5cf28e97622e` | `Lib/Geometry/Manifold/Morse/CellStructure.lean` | 53 | 4273335 D2 |
| `Hopf/Recognition.lean:3538-3715` | `34a8debb8ce33078b1f28292037092166388ba84cd74672f5c0565d37527598c` | `Lib/Geometry/Manifold/Morse/CellStructure.lean` | 7 | 4273335 D2 |
| `Hopf/DifferentialTopology.lean:28344-30921` | `4434e070cdfb91441f6a156bf37d63836057da5174fb150255ee4acefa2cc036` | `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | 116 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:9043-10576` | `ebf559564864ddeedc73bf4f8a0050c885e27c86a3aa516202ba84da32a2249a` | `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` | 103 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:13902-14130` | `fc6fc11d9a804eb935d7b77dfaf4bd9203d7329e7ddc8ffdf73734ff614fb81a` | `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` | 16 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:20996-23748` | `d6f68c6f00dd85ec28553106f1c13a5c093e7898a49c3c60a8549dee27340591` | `Lib/Geometry/Manifold/Transversality/Basic.lean` | 133 | 753ecf8 D2 |
| `Hopf/DifferentialTopology.lean:11287-11601` | `beea0c76f3704d0ae3f5815f231da6011b582136a6a50d964a32a13ea795ee69` | `Lib/Geometry/Manifold/VectorBundle/ProjectionBundle.lean` | 31 | 488c283 D2 |
| `Hopf/DifferentialTopology.lean:10577-11286` | `86ffbe7d86d30d6f24b53d9607b663d84de7cfa56c94420d30b8a96b534c4a8a` | `Lib/Geometry/Manifold/WhitneyEmbedding.lean` | 51 | 488c283 D2 |
| `Hopf/SingularHomology.lean:28353-28954` | `8495b3baa2f99e1156c74ef4464f46913d37da204b56f736b75d05747d4f6c21` | `Lib/Topology/Homotopy/CellAttachment.lean` | 59 | cf18527 D2 |
| `Hopf/SingularHomology.lean:29032-29600` | `561cf5c2ff512c54d72cc217abdc3f5fc9b4b6c863c4af9d41f0bf3c278e3330` | `Lib/Topology/Homotopy/CellAttachment.lean` | 73 | cf18527 D2 |
| `Hopf/LCP/PeriodConstruction.lean:15593-15601` | `edfa15504ca7b9a83b60d3a7de9a858a3b0f5282a3c792baeceaa6a0ba4000b3` | `Lib/Analysis/Complex/Cousin.lean` | 2 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:16409-17286` | `ebf6829496bf6f023437792f0f5754ce6b03b6fb3a975ca7e0d5cc6b98527ee3` | `Lib/Analysis/Complex/Cousin.lean` | 93 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:3581-4028` | `a28ac7da24f9197cc36e0995cb799aec348f0f76bd15df403e2f936b23456e78` | `Lib/Analysis/Complex/Mobius.lean` | 54 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:4149-4275` | `f96a1298f592b0588f70da4db97cdb550ca065a0184fe82acd1bb9fd496487fb` | `Lib/Analysis/Complex/RiemannMapping.lean` | 14 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:4369-4568` | `cc6aa36264c0de76b581246b2eaaaa0799fd3994d7a8aa44b33780b759925ae3` | `Lib/Analysis/Complex/RiemannMapping.lean` | 26 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:4615-4710` | `aca0a5d3dbb4bf49bb1b58e45b6361bcef8c2a6a6a1e4326d6dab90d78737619` | `Lib/Analysis/Complex/RiemannMapping.lean` | 8 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:4968-5060` | `c9ac7fea8c8a889ab3d53661e9d5be5781f97b10e6b1fd641a0c48d5a0c3cf94` | `Lib/Analysis/Complex/RiemannMapping.lean` | 5 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:5414-5535` | `d75ef12c2ec64e8d6b316b43f005c1f18040e014ecf0c72c71d8188f8deb6e62` | `Lib/Analysis/Complex/RiemannMapping.lean` | 6 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:5559-5572` | `d9f2921ee98793c907517b2b944bec3d28a2024a6e0c015fa5b61a338db09c7c` | `Lib/Analysis/Complex/RiemannMapping.lean` | 3 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:6195-6429` | `ecc69c5052614bcb24af34a7bb4c730e85c43df1456cab4f0dc9128fffc3c409` | `Lib/Analysis/Complex/RiemannMapping.lean` | 17 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:6600-7062` | `7a3bddc0959b6f9ec5ea09ddbb174773fbd1acfadc01548d2f155f4fcc91483e` | `Lib/Analysis/Complex/RiemannMapping.lean` | 26 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:7085-7097` | `807e5d0282fc2ba07b42d4b514327a04a6d06ca0470bd54513c0cfc1866456a6` | `Lib/Analysis/Complex/RiemannMapping.lean` | 1 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:7297-7624` | `29aeaf8a27a5555d1717a3508f6f2417375eca163a11f1e4fbf1da8bd43310a4` | `Lib/Analysis/Complex/RiemannMapping.lean` | 43 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:7795-7952` | `7256b9fa231043980c937e6e6538e77a3ce1aa4c0e92e392a4c5d1b5abebb211` | `Lib/Analysis/Complex/RiemannMapping.lean` | 8 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:8067-8178` | `a9f84e14a14ed068d3964311828dbd3f1d31dbd05209d017fbf8e4ed42fb1fd1` | `Lib/Analysis/Complex/RiemannMapping.lean` | 7 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:8326-8442` | `ab42cfaa20f641dd07f23f7531faf1b940a4ca2b376f4be026491319c00b3335` | `Lib/Analysis/Complex/RiemannMapping.lean` | 10 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:8557-8570` | `51431aee01fb059645e29c0455384d9ee0ced34c4ef56ecb245d6a4fdf86b213` | `Lib/Analysis/Complex/RiemannMapping.lean` | 3 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:9099-9135` | `e3f4f2f6de0dcdd8bed01ff5f307416753df32f8059a27221aec2da90d5ac272` | `Lib/Analysis/Complex/RiemannMapping.lean` | 4 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:4711-4967` | `8ef330ad8a5906332fd403e31cb4fa2120c6efcad687aa60c098014b4b8ceaa8` | `Lib/Analysis/Complex/RiemannMapping/Steps.lean` | 4 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:5061-5413` | `2dca922074b6aed6668116cdb09dc0f7ceaedf1c4244f26d1e265c43a729d0d5` | `Lib/Analysis/Complex/RiemannMapping/Steps.lean` | 27 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:6430-6599` | `e117c9662ade87ab6e36d571ab15615d5850bdb42c869fb7cf6967c9dccfb71d` | `Lib/Analysis/Complex/SchwarzReflection.lean` | 16 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:10071-10098` | `3a393b9066b41c5e46ffde21f221da0c6c42e82dcbdaf9156e150a1b9a5d1a1d` | `Lib/Analysis/Complex/SquareRoot.lean` | 1 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:12060-12220` | `7afd135606639aa6a47a4f582f935be58160e6beda81c5885fe8dc906d7906ec` | `Lib/Analysis/Complex/SquareRoot.lean` | 24 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:12576-12786` | `1f3bd7549dfca014a1bce9aefadd458aac539d59aef02266ceb7d1fde63fe3ef` | `Lib/Analysis/Complex/SquareRoot.lean` | 16 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:12909-13107` | `ac9e4c435121aae40a5add598db64c3948907009499095c271886cabc9fa66c3` | `Lib/Analysis/Complex/SquareRoot.lean` | 17 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:13188-13240` | `53185febcbe0da1e66cd239072e1c13a509b664c985457dfbe19ecbfdc564866` | `Lib/Analysis/Complex/SquareRoot.lean` | 4 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:11975-12022` | `c6ffa4da878daecd79f6172cc7e873ca4e0760b175488d13fac5c66112a0a060` | `Lib/Geometry/Manifold/Complex/Biholomorph.lean` | 2 | 685fd91 H |
| `Hopf/LCP/AnalyticFillings.lean:12124-12220` | `ecb789dd050fe573bdb124809c46d50e344d9d5fe7194bbab39e69835959154b` | `Lib/Geometry/Manifold/Complex/Biholomorph.lean` | 5 | 685fd91 H |
| `Hopf/LCP/PeriodConstruction.lean:7757-8084` | `70af88f472628923427062003123541c65cae8acbd39029a85bf2afc5310aaa7` | `Lib/Geometry/Manifold/Instances/RiemannSphere.lean` | 37 | 685fd91 H |
| `Hopf/Hurewicz.lean:2264-2267` | `4fa712f5b44257d81d3f4b4fef722360d0496bdf9152b101c9b851e6c62aee6a` | `Lib/AlgebraicTopology/SingularHomology/CrossInsert.lean` | 1 | 5e9a74e I |
| `Hopf/Hurewicz.lean:2272-2289` | `71b67cb3d6228634511a0c2c2ae06176d53fd060877d4af543bc5514e60547d5` | `Lib/AlgebraicTopology/SingularHomology/CrossInsert.lean` | 2 | 5e9a74e I |
| `Hopf/LCP/CuspFilling.lean:8877-9135` | `e198d1aebdd22c63169e1c01b8d92386a376be172bb745b5ef9a95821eb4d6c4` | `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` | 43 | 5e9a74e I |
| `Hopf/LCP/CuspFilling.lean:9142-9163` | `82f1e9df83200cf75274c496a0a96373a287b23f87af607e3ac7da396cdc4138` | `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` | 4 | 5e9a74e I |
| `Hopf/LCP/CuspFilling.lean:9203-9245` | `e8e399a649dfd86184abb19e34806d4e687750c2a79bd73a2eb5881040ef3d0d` | `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` | 5 | 5e9a74e I |
| `Hopf/LCP/CuspFilling.lean:9290-9302` | `d1f1caa51e23753ee713a09baa06109300d01118ef838a667a610554ebd0a3c0` | `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` | 2 | 5e9a74e I |
| `Hopf/LCP/CuspFilling.lean:13990-14014` | `6bde737f0a3732fae31f1d6e72aa4c485b57ed027be6cab242252a3049656deb` | `Lib/AlgebraicTopology/SingularHomology/PathClass.lean` | 4 | 5e9a74e I |
| `Hopf/LCP/PeriodConstruction.lean:85-137` | `2858e14c4c3d52328d2a3f2ad27a3745994d59cfcad30f675ea64b56307d33ac` | `Lib/Geometry/Manifold/Quotient/Atlas.lean` | 6 | 91dc733 I |
| `Hopf/LCP/PeriodConstruction.lean:182-326` | `e1487146d630844799e2efba3926d45187921d28fea50fc617c3f13769c74224` | `Lib/Geometry/Manifold/Quotient/Atlas.lean` | 16 | 91dc733 I |
| `Hopf/LCP/PeriodConstruction.lean:3232-3351` | `4f8e17820567af33d8831dc31f4600a5408cc0bdd6daa7f5b6ee4744be8eb953` | `Lib/Geometry/Manifold/Quotient/LocalOrbit.lean` | 17 | 91dc733 I |
| `Hopf/LCP/BoundaryTopology.lean:23691-23756` | `fb4575804ab84d7ebf60a23c3d344d6a4b8af4ed98bff46585478a167bc2ee68` | `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` | 13 | 6f66a42 I |
| `Hopf/LCP/BoundaryTopology.lean:23768-23780` | `7ae7dd6967a4410948305fde584983a83b92a2dfc3a2236ad0790826fa65ffd0` | `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` | 1 | 6f66a42 I |
| `Hopf/LCP/BoundaryTopology.lean:23787-23819` | `decce72f946df827ce2401224db4924e41ede71c8263664294b65d346bdf8e3e` | `Lib/GroupTheory/PresentedGroup/CentralTwist.lean` | 6 | 6f66a42 I |
| `Hopf/LCP/BoundaryTopology.lean:14723-14827` | `f28721ef9a6db001bfac1f1725e5ed6b4b7c08446f752eb14092bf47c1658edb` | `Lib/GroupTheory/SplitExtension.lean` | 13 | fa74283 I |
| `Hopf/LCP/PeriodConstruction.lean:2958-3056` | `f2ba581a6b07f28f1de72a7eb29e2d545a711870fbf818e511f5d0b23ae029b1` | `Lib/Topology/Algebra/FreeActionLocus.lean` | 13 | 867880d I |
| `Hopf/LCP/AnalyticFillings.lean:1118-1467` | `3bcff51793cde1699474207c7d7d63026dbd7810a55a99b71f2cb0f91ee2c2d0` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 41 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:11136-11141` | `88d763f022ff40552b11bb8f939c87236f986a305292235931ff7547d71a9b0a` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 1 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:12979-12984` | `2123de67d57d5731ab48846d5f4957ff5a36f43c4eaffe3e2d9fa5ea9818e055` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 1 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:14239-14338` | `8ab7d86bb06ca468f08c70905200a73c5178c3b5f39826b8784e78534959e90e` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 12 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:14407-14645` | `41053cac087203fb883f17509f151c91f6b26748b2c7b6209227572b01dc8d7e` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 9 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:17579-17679` | `eab02886b8e00b90cb12b095dbafde47dba461a351b0bebfae9563a7c700ce1e` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 10 | 1303c4a I |
| `Hopf/LCP/BoundaryTopology.lean:21863-21918` | `aae994fe6457b2b4fb3ed9a622d0a6d54594c25761af040cfab55c15983f53c4` | `Lib/Topology/Covering/DiagonalQuotient.lean` | 4 | 1303c4a I |
| `Hopf/LCP/CuspFilling.lean:797-831` | `5923adf2b1c2dba58cfd834a12f39357f0447b91018958a863c3fba5b592458c` | `Lib/Topology/Covering/InvariantSubset.lean` | 5 | 26f5ffd I |
| `Hopf/LCP/CuspFilling.lean:1524-1661` | `f8ea22578e4705e8a783c41dbf0a1c44cd042be9542cd61d1d8a9e3866a7295f` | `Lib/Topology/Covering/InvariantSubset.lean` | 14 | 26f5ffd I |
| `Hopf/LCP/LocalModels.lean:231-367` | `9e6c32675687d07753307b9aca6f1dbd6729984813b110384377ca825c1eaa62` | `Lib/Topology/Covering/Quotient.lean` | 13 | 4e0bb8e I |
| `Hopf/LCP/LocalModels.lean:570-583` | `53327116d71fc1358890909aac63dc459558f81ce3457dfed2cb46e7b2ad0e03` | `Lib/Topology/Covering/Quotient.lean` | 1 | 4e0bb8e I |
| `Hopf/LCP/LocalModels.lean:2551-2561` | `99f964460b8b7ec6394adf77ce5133385c4de84b80e66f31baac19ab67f5a81d` | `Lib/Topology/Covering/Quotient.lean` | 1 | 4e0bb8e I |
| `Hopf/LCP/LocalModels.lean:2589-2819` | `a9dab89ada6328a402e635a07a20426e5c0441774868323da585e45e4680fbbd` | `Lib/Topology/Covering/Quotient.lean` | 16 | 4e0bb8e I |
| `Hopf/LCP/LocalModels.lean:4538-4564` | `80b8beb2bd3447f555d5a61207ad1bea3916924575d89beada2af97cebd70e50` | `Lib/Topology/Covering/Quotient.lean` | 1 | 4e0bb8e I |
| `Hopf/LCP/BoundaryTopology.lean:9537-9686` | `2cd87a5647bc60030ac422b5db9d67247b18a6b69a18e86851703ce9698eb3fa` | `Lib/Topology/FiberBundle/TwoOpenTransition.lean` | 24 | 82a568a I |
| `Hopf/LCP/BoundaryTopology.lean:9790-9989` | `7bdb2d4a0d7a9b87f058434cd48f4b2e7b65e5a2eff0c8111ce6356564fc64be` | `Lib/Topology/FiberBundle/TwoOpenTransition.lean` | 22 | 82a568a I |
| `Hopf/LCP/CuspFilling.lean:490-627` | `43f1fa15cd973f3209779c6a8ed5d369fd913c2b99aa36c419728ed54669c518` | `Lib/Topology/Homotopy/LocalCollapse.lean` | 11 | b0a1029 I |
| `Hopf/LCP/LocalModels.lean:8731-8924` | `95141c3b5d7ebaedcf58edd9859c5108ca6ad91457b666471481b43c8d269188` | `Lib/Topology/Homotopy/SublevelRetraction.lean` | 22 | dfad079 I |
| `Hopf/LCP/LocalModels.lean:6899-7036` | `660516c5346ec90c68cb2e3867ca18149d7efccfb49868bb2252606c04a8668f` | `Lib/Topology/MappingTorus/Basic.lean` | 22 | 79211df I |
| `Hopf/LCP/LocalModels.lean:7984-8395` | `6d95645f1de1fa92b32d6838388bd216b50a0481fd55ef0ccfac27a2d550b243` | `Lib/Topology/MappingTorus/Basic.lean` | 54 | 79211df I |
| `Hopf/LCP/BoundaryTopology.lean:3988-4609` | `4e0ed08f80cc446cf4a09c0082d0f2800315f965b7e55ee68589f502f58e9aca` | `Lib/Topology/MappingTorus/HomologyCover.lean` | 58 | d92f3cf I |

## Public-module conversion and first G/E2/F/J moves after `bbf1dd2`

Seat: Devin. Batch based on `bbf1dd2`, split into provider-conversion, J-naturality, G/F-extraction and documentation commits. This addendum supersedes older legacy-provider claims only for the scope below; it does not certify the remaining lane packets.

- The geometric provider cone through `Morse/Rearrangement.lean` is now `module`/`public`: Handle, MorseLemma, ChartedSpace/Transport, Flow/Compact, RegularLevel, HandleAttachment, HeightTranslating, Existence, SmoothFlow, HandleRetraction, SublevelSets, Index, CylinderHEP, WhitneyEmbedding, ProjectionBundle, Collar, SurgeryWindows, Cancellation, Transversality/Basic, Immersion/Relative, Rearrangement. LoopSubdivision and SimplyConnectedSphere were also converted. All original theorem statements and FQNs are retained.
- Module-opacity adaptations: private `import all` access to the defining Mathlib modules where needed; an exposed field-for-field diffeomorphism-to-partial-diffeomorphism constructor used by `translateChart`; a literal-existential helper theorem used by `partialDiffeomorphOfInjectiveLocal`; and an inner proof binding in `bumpTranslation_apply`. Ordinary importing consumers do not need `import all`. No Mathlib package or theorem statement was changed.
- J S-nat: `CuspFilling.lean` at `bbf1dd2`, lines 14295–14475, moved to `CircleProduct.lean`; S-cross: lines 14477–14546 moved to `CrossProduct.lean`. Public output names remain `PeriodTorusHigherHomology.*`; references to existing shim aliases were replaced by their actual Lib providers. The source declarations were removed and CuspFilling imports the public providers.
- F2 initial model: `SingularHomology.lean` at `bbf1dd2`, lines 11700–11705 and 12354–12766, moved verbatim to `Lib/Geometry/Manifold/Whitney/BigonModel.lean`. This is the explicit bigon/strip-coordinate model, not all of F2 or the Whitney cancellation campaign.
- G1: `SingularHomology.lean` at `bbf1dd2`, lines 14044–14055, and `SphereTopology.lean:14166–14171` moved to `Lib/Geometry/Manifold/Morse/MinimalSystem.lean`. The latter proof now names the actual `SingularHomology.homotopyEquivHomologyEquiv` provider. This supplies `SixSphere` and the three G1 facts, not G2a–G6. Both new files are registered in `Lib.lean`; SH/ST import them instead of defining duplicates.

### Verification and evidence

All five default roots (`Lib.lean`, `Solution.lean`, `S6Shortcuts.lean`, `S6.lean`, `Challenge.lean`) compiled successfully using direct Lean 4.33.0 with local output artifacts. The only recorded warning was the existing `Challenge.lean:42` use of `sorry`; Challenge was not modified. The full source-consumer chain, including Recognition and Final, compiled. An ordinary module aggregate importing Rearrangement, BigonModel, MinimalSystem, CircleProduct and CrossProduct passed its 21 API checks; the separate J consumer checked all 18 moved outputs. The current recognition and signed-Morse-chart theorems report only `[propext, Classical.choice, Quot.sound]`, not `sorryAx`. No pre-change axiom comparison is claimed.

Evidence directory: `Lib/docs/logs/devin/modconv-batch3/` (in-tree copy of the run's `/tmp` evidence; the paths below are relative to it; `*.lean` probe sources carry a `.txt` suffix in-tree so the stock census does not read them as code). `gate/build.sh` records the direct-build recipe; `gate/driver.log` and `gate/driver2.log` record the initial stale-artifact failure and successful continuation after fixing dependency traversal; `gate/ProbeAggregate.lean`/`.log` and `gate/ProbeAxioms.lean`/`.log` record the probes. `cone/ProbeJ.log`, `cone/CuspFilling-final.log` and `fg/` hold focused consumer and move-preservation evidence.

Lake commands were stopped after the resolver attempted to delete/re-clone shared Mathlib on a URL-mismatch diagnostic; permission prevented it. Direct Lean was used instead. The environment owner still needs to resolve that issue; do not run package-update/cache/clean commands or modify the shared checkout to reproduce this batch.

Verified Git blob IDs for selected outputs (before this documentation-only addition):

| File | Git blob |
|---|---|
| `Lib/Geometry/Manifold/Whitney/BigonModel.lean` | `f02a3cb92ca8012e56e486f314d268b8e980efab` |
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | `d2f15ef98cfb4b387ddfcc8fd89cf489f058354a` |
| `Lib/Geometry/Manifold/Morse/Rearrangement.lean` | `accfb2948a10a05b282f7e3da96c5c26471089f8` |
| `Lib/AlgebraicTopology/SingularHomology/CircleProduct.lean` | `c7c7a05e4a2744e7c44afa979658d7f5015e6c6d` |
| `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` | `00579852caff6ddb2be104bca436f41e67ea5e98` |

### Still open

G2a–G6 and the remaining F geometric/Whitney/slide blocks are not moved by this batch. J's circle-path/section cluster and higher coordinate/exterior boundaries remain unfinished; G-J3 was already public in CrossProduct before this batch, not newly moved here. E2's remaining Hopf-side outputs and proposed general-k implementation are not covered by provider conversion. Exact remaining helper packets, complete textbook module documentation, current ledgers/coordinates, independent acceptance and lane-level receipts still need completion. A green conversion batch is not a whole-lane Axis-5/6 certification.

## Integration-3 seat receipts (Muse/Devin), head `84d9450`

Branch `lib/textbook-extraction-muse-i3`, based on upstream `27f8e7f` per
`NEXT-STEPS-MUSE.md` and `Lib/reviews/INTEGRATION-3.md` §3.

- **Lake build**: `lake build` (SEAT-SETUP recipe, `GIT_CONFIG_*` set) completed
  8854 jobs over the post-`import all`-cleanup code (`840aef4`; subsequent
  commits are doc-only). `Solution.lean` reports the standard axiom set
  `[propext, Classical.choice, Quot.sound]` only.
- **Census ratchet**: `scripts/lib_stock_census.py` → `ratchet OK: 1648 <= baseline 1648`.
- **Off-tree citations** (`0ab4a4a`): review-file `/home/ox-alpha/...` paths
  repointed to in-tree copies (with a disclosure line per file); RECEIPTS
  `/tmp/sidekick-modconv-batch3-*/` evidence copied to
  `Lib/docs/logs/devin/modconv-batch3/` (`*.lean` → `*.lean.txt`); J ledger
  `~/s6-notes/J-review*.md` citations repointed to the in-tree
  `Lib/docs/J-axis5-review*.md`/`J-stage2-review.md`.
- **Module docstrings** (`1ebcb45`): `Morse/MinimalSystem.lean`,
  `Whitney/BigonModel.lean`.
- **`import all` removal** (`840aef4`): `Transversality/Basic.lean` and
  `Immersion/Relative.lean` now use `public import` only. Because module
  importers cannot unfold Mathlib's non-`@[expose]` bodies, Basic adds two
  transparent Lib replacements (`Diffeomorph.toPartialDiffeomorph'`,
  `IsLocalDiffeomorph.diffeomorph'`, both outside `namespace
  Mathoverflow1973`) built on `PartialEquiv` literals, `Equiv.ofBijective`,
  and the public `localInverse` API; Relative uses the public constructor
  `PartialDiffeomorph.isLocalDiffeomorphAt` at the two literal-existential
  sites. The remaining `import all` lines sit in GLM-owned files.
- **E2 closing review**: `Lib/docs/E2-closing-subagent-review.md` — GO at
  `840aef4` (22/22 signatures verbatim; coordinate drift corrected).
- **G closing review**: `Lib/docs/G-closing-subagent-review.md` — NO-GO (one
  residual truncation + four minors), all repaired; re-confirmation chain in
  `Lib/docs/G-closing-reconfirm-subagent-review.md` — GO at `66d04dc`.
- **Ledger refresh** (`2cb2117`, `6a8e4a8`): E2/G signature blocks regenerated
  verbatim against post-proof-split, post-rename sources; all coordinate
  comments re-verified.
- **E2 Axis-5 review**: `Lib/docs/E2-axis5-subagent-review.md` — initial NO-GO
  (residual coordinate drift in the §13 table and two ledger comments after the
  `840aef4` insertions); repairs at `d4038e1`; re-confirmation GO → ledger
  marked accepted at `88e354b`.
- **G Axis-5 review**: `Lib/docs/G-axis5-subagent-review.md` — GO at `84d9450`
  (35/35 signatures verbatim, current names clean); ledger marked accepted at
  `ac6c338`.
- **J Axis-5 review**: `Lib/docs/J-axis5-i3-review.md` — initial NO-GO (stale
  pre-move coordinates throughout, LibShims-only `crossProductHomology`
  spellings, undisclosed `coordinatePeriodLoop` binder rename, stale
  S-nat/S-cross/G-J3 seam claims); two repair rounds; first re-confirmation
  found six residual defects (false `CirclePaths` Lib-provider claim,
  wrong-path rank-3 re-run described as deleted, shifted block ranges,
  nonexistent `Hopf.FiniteCore` consumer path, truncated G-J3 range, one wrong
  coordinate) — all repaired; second re-confirmation GO. Ledger consistent at
  `90cd3d9`. Scoped: Axis-5 consistency only — J-B/J-C/J-D/J-E uncertified,
  J-B2a still blocked on the unlanded S-path cluster.
