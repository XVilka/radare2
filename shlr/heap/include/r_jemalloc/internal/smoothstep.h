/*
 * This file was generated by the following command:
 *   sh smoothstep.sh smoother 200 24 3 15
 */
/******************************************************************************/
#ifdef JEMALLOC_H_TYPES

/*
 * This header defines a precomputed table based on the smoothstep family of
 * sigmoidal curves (https://en.wikipedia.org/wiki/Smoothstep) that grow from 0
 * to 1 in 0 <= x <= 1.  The table is stored as integer fixed point values so
 * that floating point math can be avoided.
 *
 *                      3     2
 *   smoothstep(x) = -2x  + 3x
 *
 *                       5      4      3
 *   smootherstep(x) = 6x  - 15x  + 10x
 *
 *                          7      6      5      4
 *   smootheststep(x) = -20x  + 70x  - 84x  + 35x
 */

#define SMOOTHSTEP_VARIANT "smoother"
#define SMOOTHSTEP_NSTEPS 200
#define SMOOTHSTEP_BFP 24
#define SMOOTHSTEP                                                          \
	/* STEP(step, h,                            x,     y) */            \
	STEP (1, UINT64_C (0x0000000000000014), 0.005, 0.000001240643750)   \
	STEP (2, UINT64_C (0x00000000000000a5), 0.010, 0.000009850600000)   \
	STEP (3, UINT64_C (0x0000000000000229), 0.015, 0.000032995181250)   \
	STEP (4, UINT64_C (0x0000000000000516), 0.020, 0.000077619200000)   \
	STEP (5, UINT64_C (0x00000000000009dc), 0.025, 0.000150449218750)   \
	STEP (6, UINT64_C (0x00000000000010e8), 0.030, 0.000257995800000)   \
	STEP (7, UINT64_C (0x0000000000001aa4), 0.035, 0.000406555756250)   \
	STEP (8, UINT64_C (0x0000000000002777), 0.040, 0.000602214400000)   \
	STEP (9, UINT64_C (0x00000000000037c2), 0.045, 0.000850847793750)   \
	STEP (10, UINT64_C (0x0000000000004be6), 0.050, 0.001158125000000)  \
	STEP (11, UINT64_C (0x000000000000643c), 0.055, 0.001529510331250)  \
	STEP (12, UINT64_C (0x000000000000811f), 0.060, 0.001970265600000)  \
	STEP (13, UINT64_C (0x000000000000a2e2), 0.065, 0.002485452368750)  \
	STEP (14, UINT64_C (0x000000000000c9d8), 0.070, 0.003079934200000)  \
	STEP (15, UINT64_C (0x000000000000f64f), 0.075, 0.003758378906250)  \
	STEP (16, UINT64_C (0x0000000000012891), 0.080, 0.004525260800000)  \
	STEP (17, UINT64_C (0x00000000000160e7), 0.085, 0.005384862943750)  \
	STEP (18, UINT64_C (0x0000000000019f95), 0.090, 0.006341279400000)  \
	STEP (19, UINT64_C (0x000000000001e4dc), 0.095, 0.007398417481250)  \
	STEP (20, UINT64_C (0x00000000000230fc), 0.100, 0.008560000000000)  \
	STEP (21, UINT64_C (0x0000000000028430), 0.105, 0.009829567518750)  \
	STEP (22, UINT64_C (0x000000000002deb0), 0.110, 0.011210480600000)  \
	STEP (23, UINT64_C (0x00000000000340b1), 0.115, 0.012705922056250)  \
	STEP (24, UINT64_C (0x000000000003aa67), 0.120, 0.014318899200000)  \
	STEP (25, UINT64_C (0x0000000000041c00), 0.125, 0.016052246093750)  \
	STEP (26, UINT64_C (0x00000000000495a8), 0.130, 0.017908625800000)  \
	STEP (27, UINT64_C (0x000000000005178b), 0.135, 0.019890532631250)  \
	STEP (28, UINT64_C (0x000000000005a1cf), 0.140, 0.022000294400000)  \
	STEP (29, UINT64_C (0x0000000000063498), 0.145, 0.024240074668750)  \
	STEP (30, UINT64_C (0x000000000006d009), 0.150, 0.026611875000000)  \
	STEP (31, UINT64_C (0x000000000007743f), 0.155, 0.029117537206250)  \
	STEP (32, UINT64_C (0x0000000000082157), 0.160, 0.031758745600000)  \
	STEP (33, UINT64_C (0x000000000008d76b), 0.165, 0.034537029243750)  \
	STEP (34, UINT64_C (0x0000000000099691), 0.170, 0.037453764200000)  \
	STEP (35, UINT64_C (0x00000000000a5edf), 0.175, 0.040510175781250)  \
	STEP (36, UINT64_C (0x00000000000b3067), 0.180, 0.043707340800000)  \
	STEP (37, UINT64_C (0x00000000000c0b38), 0.185, 0.047046189818750)  \
	STEP (38, UINT64_C (0x00000000000cef5e), 0.190, 0.050527509400000)  \
	STEP (39, UINT64_C (0x00000000000ddce6), 0.195, 0.054151944356250)  \
	STEP (40, UINT64_C (0x00000000000ed3d8), 0.200, 0.057920000000000)  \
	STEP (41, UINT64_C (0x00000000000fd439), 0.205, 0.061832044393750)  \
	STEP (42, UINT64_C (0x000000000010de0e), 0.210, 0.065888310600000)  \
	STEP (43, UINT64_C (0x000000000011f158), 0.215, 0.070088898931250)  \
	STEP (44, UINT64_C (0x0000000000130e17), 0.220, 0.074433779200000)  \
	STEP (45, UINT64_C (0x0000000000143448), 0.225, 0.078922792968750)  \
	STEP (46, UINT64_C (0x00000000001563e7), 0.230, 0.083555655800000)  \
	STEP (47, UINT64_C (0x0000000000169cec), 0.235, 0.088331959506250)  \
	STEP (48, UINT64_C (0x000000000017df4f), 0.240, 0.093251174400000)  \
	STEP (49, UINT64_C (0x0000000000192b04), 0.245, 0.098312651543750)  \
	STEP (50, UINT64_C (0x00000000001a8000), 0.250, 0.103515625000000)  \
	STEP (51, UINT64_C (0x00000000001bde32), 0.255, 0.108859214081250)  \
	STEP (52, UINT64_C (0x00000000001d458b), 0.260, 0.114342425600000)  \
	STEP (53, UINT64_C (0x00000000001eb5f8), 0.265, 0.119964156118750)  \
	STEP (54, UINT64_C (0x0000000000202f65), 0.270, 0.125723194200000)  \
	STEP (55, UINT64_C (0x000000000021b1bb), 0.275, 0.131618222656250)  \
	STEP (56, UINT64_C (0x0000000000233ce3), 0.280, 0.137647820800000)  \
	STEP (57, UINT64_C (0x000000000024d0c3), 0.285, 0.143810466693750)  \
	STEP (58, UINT64_C (0x0000000000266d40), 0.290, 0.150104539400000)  \
	STEP (59, UINT64_C (0x000000000028123d), 0.295, 0.156528321231250)  \
	STEP (60, UINT64_C (0x000000000029bf9c), 0.300, 0.163080000000000)  \
	STEP (61, UINT64_C (0x00000000002b753d), 0.305, 0.169757671268750)  \
	STEP (62, UINT64_C (0x00000000002d32fe), 0.310, 0.176559340600000)  \
	STEP (63, UINT64_C (0x00000000002ef8bc), 0.315, 0.183482925806250)  \
	STEP (64, UINT64_C (0x000000000030c654), 0.320, 0.190526259200000)  \
	STEP (65, UINT64_C (0x0000000000329b9f), 0.325, 0.197687089843750)  \
	STEP (66, UINT64_C (0x0000000000347875), 0.330, 0.204963085800000)  \
	STEP (67, UINT64_C (0x0000000000365cb0), 0.335, 0.212351836381250)  \
	STEP (68, UINT64_C (0x0000000000384825), 0.340, 0.219850854400000)  \
	STEP (69, UINT64_C (0x00000000003a3aa8), 0.345, 0.227457578418750)  \
	STEP (70, UINT64_C (0x00000000003c340f), 0.350, 0.235169375000000)  \
	STEP (71, UINT64_C (0x00000000003e342b), 0.355, 0.242983540956250)  \
	STEP (72, UINT64_C (0x0000000000403ace), 0.360, 0.250897305600000)  \
	STEP (73, UINT64_C (0x00000000004247c8), 0.365, 0.258907832993750)  \
	STEP (74, UINT64_C (0x0000000000445ae9), 0.370, 0.267012224200000)  \
	STEP (75, UINT64_C (0x0000000000467400), 0.375, 0.275207519531250)  \
	STEP (76, UINT64_C (0x00000000004892d8), 0.380, 0.283490700800000)  \
	STEP (77, UINT64_C (0x00000000004ab740), 0.385, 0.291858693568750)  \
	STEP (78, UINT64_C (0x00000000004ce102), 0.390, 0.300308369400000)  \
	STEP (79, UINT64_C (0x00000000004f0fe9), 0.395, 0.308836548106250)  \
	STEP (80, UINT64_C (0x00000000005143bf), 0.400, 0.317440000000000)  \
	STEP (81, UINT64_C (0x0000000000537c4d), 0.405, 0.326115448143750)  \
	STEP (82, UINT64_C (0x000000000055b95b), 0.410, 0.334859570600000)  \
	STEP (83, UINT64_C (0x000000000057fab1), 0.415, 0.343669002681250)  \
	STEP (84, UINT64_C (0x00000000005a4015), 0.420, 0.352540339200000)  \
	STEP (85, UINT64_C (0x00000000005c894e), 0.425, 0.361470136718750)  \
	STEP (86, UINT64_C (0x00000000005ed622), 0.430, 0.370454915800000)  \
	STEP (87, UINT64_C (0x0000000000612655), 0.435, 0.379491163256250)  \
	STEP (88, UINT64_C (0x00000000006379ac), 0.440, 0.388575334400000)  \
	STEP (89, UINT64_C (0x000000000065cfeb), 0.445, 0.397703855293750)  \
	STEP (90, UINT64_C (0x00000000006828d6), 0.450, 0.406873125000000)  \
	STEP (91, UINT64_C (0x00000000006a842f), 0.455, 0.416079517831250)  \
	STEP (92, UINT64_C (0x00000000006ce1bb), 0.460, 0.425319385600000)  \
	STEP (93, UINT64_C (0x00000000006f413a), 0.465, 0.434589059868750)  \
	STEP (94, UINT64_C (0x000000000071a270), 0.470, 0.443884854200000)  \
	STEP (95, UINT64_C (0x000000000074051d), 0.475, 0.453203066406250)  \
	STEP (96, UINT64_C (0x0000000000766905), 0.480, 0.462539980800000)  \
	STEP (97, UINT64_C (0x000000000078cde7), 0.485, 0.471891870443750)  \
	STEP (98, UINT64_C (0x00000000007b3387), 0.490, 0.481254999400000)  \
	STEP (99, UINT64_C (0x00000000007d99a4), 0.495, 0.490625624981250)  \
	STEP (100, UINT64_C (0x0000000000800000), 0.500, 0.500000000000000) \
	STEP (101, UINT64_C (0x000000000082665b), 0.505, 0.509374375018750) \
	STEP (102, UINT64_C (0x000000000084cc78), 0.510, 0.518745000600000) \
	STEP (103, UINT64_C (0x0000000000873218), 0.515, 0.528108129556250) \
	STEP (104, UINT64_C (0x00000000008996fa), 0.520, 0.537460019200000) \
	STEP (105, UINT64_C (0x00000000008bfae2), 0.525, 0.546796933593750) \
	STEP (106, UINT64_C (0x00000000008e5d8f), 0.530, 0.556115145800000) \
	STEP (107, UINT64_C (0x000000000090bec5), 0.535, 0.565410940131250) \
	STEP (108, UINT64_C (0x0000000000931e44), 0.540, 0.574680614400000) \
	STEP (109, UINT64_C (0x0000000000957bd0), 0.545, 0.583920482168750) \
	STEP (110, UINT64_C (0x000000000097d729), 0.550, 0.593126875000000) \
	STEP (111, UINT64_C (0x00000000009a3014), 0.555, 0.602296144706250) \
	STEP (112, UINT64_C (0x00000000009c8653), 0.560, 0.611424665600000) \
	STEP (113, UINT64_C (0x00000000009ed9aa), 0.565, 0.620508836743750) \
	STEP (114, UINT64_C (0x0000000000a129dd), 0.570, 0.629545084200000) \
	STEP (115, UINT64_C (0x0000000000a376b1), 0.575, 0.638529863281250) \
	STEP (116, UINT64_C (0x0000000000a5bfea), 0.580, 0.647459660800000) \
	STEP (117, UINT64_C (0x0000000000a8054e), 0.585, 0.656330997318750) \
	STEP (118, UINT64_C (0x0000000000aa46a4), 0.590, 0.665140429400000) \
	STEP (119, UINT64_C (0x0000000000ac83b2), 0.595, 0.673884551856250) \
	STEP (120, UINT64_C (0x0000000000aebc40), 0.600, 0.682560000000000) \
	STEP (121, UINT64_C (0x0000000000b0f016), 0.605, 0.691163451893750) \
	STEP (122, UINT64_C (0x0000000000b31efd), 0.610, 0.699691630600000) \
	STEP (123, UINT64_C (0x0000000000b548bf), 0.615, 0.708141306431250) \
	STEP (124, UINT64_C (0x0000000000b76d27), 0.620, 0.716509299200000) \
	STEP (125, UINT64_C (0x0000000000b98c00), 0.625, 0.724792480468750) \
	STEP (126, UINT64_C (0x0000000000bba516), 0.630, 0.732987775800000) \
	STEP (127, UINT64_C (0x0000000000bdb837), 0.635, 0.741092167006250) \
	STEP (128, UINT64_C (0x0000000000bfc531), 0.640, 0.749102694400000) \
	STEP (129, UINT64_C (0x0000000000c1cbd4), 0.645, 0.757016459043750) \
	STEP (130, UINT64_C (0x0000000000c3cbf0), 0.650, 0.764830625000000) \
	STEP (131, UINT64_C (0x0000000000c5c557), 0.655, 0.772542421581250) \
	STEP (132, UINT64_C (0x0000000000c7b7da), 0.660, 0.780149145600000) \
	STEP (133, UINT64_C (0x0000000000c9a34f), 0.665, 0.787648163618750) \
	STEP (134, UINT64_C (0x0000000000cb878a), 0.670, 0.795036914200000) \
	STEP (135, UINT64_C (0x0000000000cd6460), 0.675, 0.802312910156250) \
	STEP (136, UINT64_C (0x0000000000cf39ab), 0.680, 0.809473740800000) \
	STEP (137, UINT64_C (0x0000000000d10743), 0.685, 0.816517074193750) \
	STEP (138, UINT64_C (0x0000000000d2cd01), 0.690, 0.823440659400000) \
	STEP (139, UINT64_C (0x0000000000d48ac2), 0.695, 0.830242328731250) \
	STEP (140, UINT64_C (0x0000000000d64063), 0.700, 0.836920000000000) \
	STEP (141, UINT64_C (0x0000000000d7edc2), 0.705, 0.843471678768750) \
	STEP (142, UINT64_C (0x0000000000d992bf), 0.710, 0.849895460600000) \
	STEP (143, UINT64_C (0x0000000000db2f3c), 0.715, 0.856189533306250) \
	STEP (144, UINT64_C (0x0000000000dcc31c), 0.720, 0.862352179200000) \
	STEP (145, UINT64_C (0x0000000000de4e44), 0.725, 0.868381777343750) \
	STEP (146, UINT64_C (0x0000000000dfd09a), 0.730, 0.874276805800000) \
	STEP (147, UINT64_C (0x0000000000e14a07), 0.735, 0.880035843881250) \
	STEP (148, UINT64_C (0x0000000000e2ba74), 0.740, 0.885657574400000) \
	STEP (149, UINT64_C (0x0000000000e421cd), 0.745, 0.891140785918750) \
	STEP (150, UINT64_C (0x0000000000e58000), 0.750, 0.896484375000000) \
	STEP (151, UINT64_C (0x0000000000e6d4fb), 0.755, 0.901687348456250) \
	STEP (152, UINT64_C (0x0000000000e820b0), 0.760, 0.906748825600000) \
	STEP (153, UINT64_C (0x0000000000e96313), 0.765, 0.911668040493750) \
	STEP (154, UINT64_C (0x0000000000ea9c18), 0.770, 0.916444344200000) \
	STEP (155, UINT64_C (0x0000000000ebcbb7), 0.775, 0.921077207031250) \
	STEP (156, UINT64_C (0x0000000000ecf1e8), 0.780, 0.925566220800000) \
	STEP (157, UINT64_C (0x0000000000ee0ea7), 0.785, 0.929911101068750) \
	STEP (158, UINT64_C (0x0000000000ef21f1), 0.790, 0.934111689400000) \
	STEP (159, UINT64_C (0x0000000000f02bc6), 0.795, 0.938167955606250) \
	STEP (160, UINT64_C (0x0000000000f12c27), 0.800, 0.942080000000000) \
	STEP (161, UINT64_C (0x0000000000f22319), 0.805, 0.945848055643750) \
	STEP (162, UINT64_C (0x0000000000f310a1), 0.810, 0.949472490600000) \
	STEP (163, UINT64_C (0x0000000000f3f4c7), 0.815, 0.952953810181250) \
	STEP (164, UINT64_C (0x0000000000f4cf98), 0.820, 0.956292659200000) \
	STEP (165, UINT64_C (0x0000000000f5a120), 0.825, 0.959489824218750) \
	STEP (166, UINT64_C (0x0000000000f6696e), 0.830, 0.962546235800000) \
	STEP (167, UINT64_C (0x0000000000f72894), 0.835, 0.965462970756250) \
	STEP (168, UINT64_C (0x0000000000f7dea8), 0.840, 0.968241254400000) \
	STEP (169, UINT64_C (0x0000000000f88bc0), 0.845, 0.970882462793750) \
	STEP (170, UINT64_C (0x0000000000f92ff6), 0.850, 0.973388125000000) \
	STEP (171, UINT64_C (0x0000000000f9cb67), 0.855, 0.975759925331250) \
	STEP (172, UINT64_C (0x0000000000fa5e30), 0.860, 0.977999705600000) \
	STEP (173, UINT64_C (0x0000000000fae874), 0.865, 0.980109467368750) \
	STEP (174, UINT64_C (0x0000000000fb6a57), 0.870, 0.982091374200000) \
	STEP (175, UINT64_C (0x0000000000fbe400), 0.875, 0.983947753906250) \
	STEP (176, UINT64_C (0x0000000000fc5598), 0.880, 0.985681100800000) \
	STEP (177, UINT64_C (0x0000000000fcbf4e), 0.885, 0.987294077943750) \
	STEP (178, UINT64_C (0x0000000000fd214f), 0.890, 0.988789519400000) \
	STEP (179, UINT64_C (0x0000000000fd7bcf), 0.895, 0.990170432481250) \
	STEP (180, UINT64_C (0x0000000000fdcf03), 0.900, 0.991440000000000) \
	STEP (181, UINT64_C (0x0000000000fe1b23), 0.905, 0.992601582518750) \
	STEP (182, UINT64_C (0x0000000000fe606a), 0.910, 0.993658720600000) \
	STEP (183, UINT64_C (0x0000000000fe9f18), 0.915, 0.994615137056250) \
	STEP (184, UINT64_C (0x0000000000fed76e), 0.920, 0.995474739200000) \
	STEP (185, UINT64_C (0x0000000000ff09b0), 0.925, 0.996241621093750) \
	STEP (186, UINT64_C (0x0000000000ff3627), 0.930, 0.996920065800000) \
	STEP (187, UINT64_C (0x0000000000ff5d1d), 0.935, 0.997514547631250) \
	STEP (188, UINT64_C (0x0000000000ff7ee0), 0.940, 0.998029734400000) \
	STEP (189, UINT64_C (0x0000000000ff9bc3), 0.945, 0.998470489668750) \
	STEP (190, UINT64_C (0x0000000000ffb419), 0.950, 0.998841875000000) \
	STEP (191, UINT64_C (0x0000000000ffc83d), 0.955, 0.999149152206250) \
	STEP (192, UINT64_C (0x0000000000ffd888), 0.960, 0.999397785600000) \
	STEP (193, UINT64_C (0x0000000000ffe55b), 0.965, 0.999593444243750) \
	STEP (194, UINT64_C (0x0000000000ffef17), 0.970, 0.999742004200000) \
	STEP (195, UINT64_C (0x0000000000fff623), 0.975, 0.999849550781250) \
	STEP (196, UINT64_C (0x0000000000fffae9), 0.980, 0.999922380800000) \
	STEP (197, UINT64_C (0x0000000000fffdd6), 0.985, 0.999967004818750) \
	STEP (198, UINT64_C (0x0000000000ffff5a), 0.990, 0.999990149400000) \
	STEP (199, UINT64_C (0x0000000000ffffeb), 0.995, 0.999998759356250) \
	STEP (200, UINT64_C (0x0000000001000000), 1.000, 1.000000000000000)

#endif /* JEMALLOC_H_TYPES */
/******************************************************************************/
#ifdef JEMALLOC_H_STRUCTS

#endif /* JEMALLOC_H_STRUCTS */
/******************************************************************************/
#ifdef JEMALLOC_H_EXTERNS

#endif /* JEMALLOC_H_EXTERNS */
/******************************************************************************/
#ifdef JEMALLOC_H_INLINES

#endif /* JEMALLOC_H_INLINES */
/******************************************************************************/
