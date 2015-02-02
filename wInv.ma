TFAXor[0, 0] = 0;
TFAXor[0, 1] = 1;
TFAXor[0, B] = 0;
TFAXor[1, B] = 1;
TFAXor[B, 0] = 0;
TFAXor[B, 1] = 1;
TFAXor[1, 1] = 0;
TFAXor[1, 0] = 1; 
TFAXor[B, B] = B;

BVStep[triple_, element_] := Module[
  {
   u, v, g1, g2, m, stop, sn, rs, fwdv, fwdg2, fwdm,
   ut, vt, g1t, g2t, mt, stopt, snt, rst, fwdvt, fwdg2t, fwdmt,
   ft, et,
   uba, ubb, ue,
   vba, vbb, ve,
   g1a, g1b,
   g2a, g2b,
   mt1, mt2,
   me1, me2,
   sntb1, sntb2,
   vt1, vt2,
   g2t1, g2t2,
   tail, pair
   },
  (
   Print["in1 : ", element];
   Print["in2 : ", triple];
   
   
   
   (* unpacking the current vector of bits *) 
   u 		= element[[1]];
   v 		= element[[2]];
   g1 		= element[[3]];
   g2 		= element[[4]];
   m 		= element[[5]];
   stop 	= element[[6]];
   sn 		= element[[7]];
   rs 		= element[[8]];
   fwdv 	= element[[9]];
   fwdg2 	= element[[10]];
   fwdm 	= element[[11]];
   
   (* unpacking the state pair *)
   
   ft 	= triple[[1]]; (*ft (with linear type of the iterated function) \

   					implements the non-size-increasing mechanism on Church words
   					and by using Mathematica's Fold function on lists
   					   we do not use ft but we have to grant the complexity 
   						constraint of the step function of Fold*)
   et 	= triple[[2]];
   
   tail = triple[[3]];
   
   (* et is the vector of bits current at the previous iteration step *)
   
   (* unpacking of et *)
   ut 		= et[[1]];
   vt 		= et[[2]];
   g1t 		= et[[3]];
   g2t 		= et[[4]];
   mt 		= et[[5]];
   stopt 	= et[[6]];
   snt 		= et[[7]];
   rst 		= et[[8]];
   fwdvt 	= et[[9]];
   fwdg2t 	= et[[10]];
   fwdmt 	= et[[11]];
   
   SBkwVst45NeverOccurs[] = 
   			{
	     		{u, v, g1, g2, m, stop, sn, rs, B, B, B},
    	 		{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
    		};
   
   (* we can obtain linear (in the type) 
   				copies of bits if we know 
				how many copies we need		*)
   
   Switch[u,
    1,	uba = 1 ; ubb = 1; ue  = 1,
    0,	uba = 0 ; ubb = 0; ue  = 0,
    B,	uba = B ; ubb = B; ue  = B
    ];
   
   Switch[v,
    1,	vba = 1 ; vbb = 1; ve  = 1,
    0,	vba = 0 ; vbb = 0; ve  = 0,
    B,	vba = B ; vbb = B; ve  = B
    ];
   
   Switch[g1,
    1,	g1a = 1 ; g1b = 1,
    0,	g1a = 0 ; g1b = 0,
    B,	g1a = B ; g1b = B
    ];
   
   Switch[g2,
    1,	g2a = 1 ; g2b = 1,
    0,	g2a = 0 ; g2b = 0,
    B,	g2a = B ; g2b = B
    ];
   
   Switch[snt,
    1,	sntb1 = 1 ; sntb2 = 1,
    0,	sntb1 = 0 ; sntb2 = 0,
    B,	sntb1 = B ; sntb2 = B
    ];

(*Print["rs  :",rs];
Print["stop :",stop];
Print["sn   :",sn];
Print["rst  :",rst];
*)
Print[
"stopt :",stopt,
"\nrst   :",rst,
"\nrs    :",rs,
"\nstop  :",stop,
"\nu     :",u,
"\nv     :",v];

	pair = Switch[stopt,
     	1,  branch="stopt=1";
     		{
      			{u, v, g1, g2, m, 1, sn, rs, fwdv, fwdg2, fwdm},
      			{ut, vt, g1t, g2t, mt, B, B, rst, fwdvt, fwdg2t, fwdmt}
      		},
     	0,   branch="stopt=0";
     		Switch[rs,
                1,  branch="stopt=0;rs=1;";
      				{
	       				{TFAXor[v, uba], ubb, TFAXor[g2, g1a], g1b, m, 0, 1, rs, B, B, B},
    	   				{ut, vt, g1t, g2t, mt, 0, snt, 1, B, B, B}
    				},
      			0, branch="stopt=0;rs=0;";
      				{
       					{TFAXor[u, vba], vbb, TFAXor[g1, g2a], g2b, m, 0, 0, rs, B, B, B},
       					{ut, vt, g1t, g2t, mt, 0, snt, 0, B, B, B}
       				},
      			B, branch="stopt=0;rs=B;";
      				{
       					{TFAXor[u, vba], vbb, TFAXor[g1, g2a], g2b, m, 0, B, rs, B, B, B},
						{ut, vt, g1t, g2t, mt, 0, snt, B, B, B, B}
					}
      		],
     	B, branch="stopt=B;";
     		Switch[rs,
      			1, branch="stopt=B;rs=1;";
      				{
       					{u, v, g1, g2, m, B, sn, 1, B, B, B},
       					{ut, vt, g1t, g2t, mt, B, snt, 1, B, B, B}
       	      		},
      			0, branch="stopt=B;rs=0;";
      				{
       					{u, v, g1, g2, m, B, sn, 0, B, B, B},
       					{ut, vt, g1t, g2t, mt, B, snt, 0, B, B, B}
       	      		},
      			B,  branch="stopt=B;rs=B;";
      				Switch[stop,
                        1, branch="stopt=B;rs=B;stop=1;";
       						{
        						{u, v, g1, g2, m, 1, B, B, B, B, B},
        						{ut, vt, g1t, g2t, mt, B, snt, rst, B, B, B}
        	                },
       					0, branch="stopt=B;rs=B;stop=0;";
       						Switch[u,
                                1, branch="stopt=B;rst=B;stop=0;u=1;";
        							Switch[v,
         								1, branch="stopt=B;rs=B;stop=0;u=1;v=1";
         									{
         										{TFAXor[1, 1], 1, TFAXor[g1, g2a], g2b, m, 0, B, rs, B, B, B},
         										{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
         									},
         								0, branch="stopt=B;rs=B;stop=0;u=1;v=0";
         									{
          		                           		{TFAXor[1, 0], 0, TFAXor[g1, g2a], g2b, m, 0, 0, rs, B, B, B},
          		                           		{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
          	                                },
         								B, branch="stopt=B;rs=B;stop=0;u=1;v=B";
         									SBkwVst45NeverOccurs[]
         			       			],
                                 0, branch="stopt=B;rs=B;stop=0;u=0;";
        							Switch[v,
                                        1,  branch="stopt=B;rs=B;stop=0;u=0;v=1;";
         									{
          		                           		{TFAXor[1, 0], 0, TFAXor[g2, g1a], g1b, m, 0, 1, rs, B, B, B},
          		                           		{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
											},
         								0,  branch="stopt=B;rs=B;stop=0;u=0;v=0;";
         									{
         										{TFAXor[0, 0], 0, TFAXor[g1, g2a], g2b, m, 0, B, rs, B, B, B},
          		                           		{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
											},
         								B, branch="stopt=B;rs=B;stop=0;u=0;v=B;";
         									SBkwVst45NeverOccurs[]
         			       			],
                                 B, branch="stopt=B;rs=B;stop=0;u=B;";
        							SBkwVst45NeverOccurs[]
        					],
       					B, branch="stopt=B;rs=B;stop=B;";
       						{
        						{u, v, g1, g2, m, B, B, 1, B, B, B},
        						{ut, vt, g1t, g2t, mt, stopt, snt, rst, B, B, B}
        	      			}
       				]
      		]
    ];
   
   (* create the state - a triple - to continue *)

   Print["case : ",branch];
   Print[pair];
   
   {Prepend, pair[[1]], ft[tail, pair[[2]]]}
   
 )
];

(* Backward Visit Last Step Function *)

BVLastStep[triple_] := Module[
  {
   u, v, g1, g2, m, stop, sn, rs, fwdv, fwdg2, fwdm,
   ut, vt, g1t, g2t, mt, stopt, snt, rst, fwdvt, fwdg2t, fwdmt,
   ft, et,
   uba, ubb, ue,
   gb, ge,
   mt1, mt2,
   me1, me2,
   sntb1, sntb2,
   vt1, vt2,
   g2t1, g2t2,
   tail, pair
   },
  (
   (*Print["in1 : ",element];*)
   Print["last step input : ", triple];
   
   (* unpacking the state pair *)
   
   ft = triple[[1]]; (*ft (with linear type of the iterated function)
   					implements the non-size-increasing mechanism on Church words
   					and by using Mathematica's Fold function on lists
   					   we do not use ft but we have to grant the complexity 
   						constraint of the step function of Fold*)
   et = triple[[2]];
   
   tail = triple[[3]];
   
   (* et is the vector of bits current at the previous iteration step \
*)
   
   (* unpacking of et *)
   u 		= et[[1]];
   v 		= et[[2]];
   g1 		= et[[3]];
   g2 		= et[[4]];
   m 		= et[[5]];
   stop 	= et[[6]];
   sn 		= et[[7]];
   rs 		= et[[8]];
   fwdv 	= et[[9]];
   fwdg2 	= et[[10]];
   fwdm 	= et[[11]];
   
   Switch[stop,
    1,	ft[tail, {u, v, g1, g2, m, B, B, B, B, B, B}],	
    0,
    	Switch[rs,
     		1, 
     			Switch[u,
     				1,	ua=1;ub=1;
     				0,	ua=0;ub=0;
     				B,	ua=B;ub=B;
     			];
     			Switch[g1,
     				1,	g1a=1;g1b=1;
     				0,	g1a=0;g1b=0;
     				B,	g1a=B;g1b=B;
     			];
     			ft[tail, {TFAXor[v, ua], ub, TFAXor[g2, g1a], g1b, m, B, B, B, B, B, B}],
     		0, 
     			Switch[v,
     				1,	va=1;vb=1;
     				0,	va=0;vb=0;
     				B,	va=B;vb=B;
     			];
     			Switch[g2,
     				1,	g2a=1;g2b=1;
     				0,	g2a=0;g2b=0;
     				B,	g2a=B;g2b=B;
     			];
     			ft[tail, {TFAXor[u, va], vb, TFAXor[g1, g2a], g2b, m, B, B, B, B, B, B}],
     		B, 
     			Switch[v,
     				1,	va=1;vb=1;
     				0,	va=0;vb=0;
     				B,	va=B;vb=B;
     			];
     			Switch[g2,
     				1,	g2a=1;g2b=1;
     				0,	g2a=0;g2b=0;
     				B,	g2a=B;g2b=B;
     			];
     			ft[tail, {TFAXor[u, va], vb, TFAXor[g1, g2a], g2b, m, B, B, B, B, B, B}]
      ],
    B,
    	tail
     ]
   
   )
 ];



(* Step Function of Forward Visit *)

FVStep[triple_, element_] := Module[
  {
   u, v, g1, g2, m, stop, sn, rs, fwdv, fwdg2, fwdm,
   ut, vt, g1t, g2t, mt, stopt, snt, rst, fwdvt, fwdg2t, fwdmt,
   ft, et,
   uba, ubb, ue,
   gb, ge,
   mt1, mt2,
   me1, me2,
   sntb1, sntb2,
   vt1, vt2,
   g2t1, g2t2,
   tail, pair
   },
  (
   Print["in1 : ", element];
   Print["in2 : ", triple];
   
   
(* unpacking the current vector of bits *)

   u = element[[1]];
   v = element[[2]];
   g1 = element[[3]];
   g2 = element[[4]];
   m = element[[5]];
   stop = element[[6]];
   sn = element[[7]];
   rs = element[[8]];
   fwdv = element[[9]];
   fwdg2 = element[[10]];
   fwdm = element[[11]];

(* unpacking the state pair *)
   
   ft = triple[[1]]; (* ft (with linear type of the iterated function) \
	   					implements the non-size-increasing mechanism on Church words
   						and by using Mathematica's Fold function on lists
   						we do not use ft but we have to grant the complexity 
   						constraint of the step function of Fold*)
   et = triple[[2]];
   
   tail = triple[[3]];
   
   (* et is the vector of bits current at the previous iteration step *)
   
   (* unpacking of et *)
   ut = et[[1]];
   vt = et[[2]];
   g1t = et[[3]];
   g2t = et[[4]];
   mt = et[[5]];
   stopt = et[[6]];
   snt = et[[7]];
   rst = et[[8]];
   fwdvt = et[[9]];
   fwdg2t = et[[10]];
   fwdmt = et[[11]];


(*Print["rs  :",rs];
Print["stop :",stop];
Print["sn   :",sn];
Print["rst  :",rst];
*)
Print[
"stopt :",stopt,
"\nu     :",u,
"\nsnt   :",snt,
"\nsn   :",sn,
"\nrst   :",rst,
"\nrs    :",rs,
"\ng1b   :",g1];

   (* we can obtain linear (in the type) copies of bits 
   		if we know 	how many copies we need              *)
   
   Switch[u,
    1,	uba = 1 ; ubb = 1; ue  = 1,
    0,	uba = 0 ; ubb = 0; ue  = 0,
    B,	uba = B ; ubb = B; ue  = B
    ];
   
   Switch[g1,
    1,	gb = 1 ; ge = 1,
    0,	gb = 0 ; ge = 0,
    B,	gb = B ; ge = B
    ];
   
   Switch[snt,
    1,	sntb1 = 1 ; sntb2 = 1,
    0,	sntb1 = 0 ; sntb2 = 0,
    B,	sntb1 = B ; sntb2 = B
    ];
   
   pair = Switch[stopt,
     1, branch="stopt=1";
     	{
      		{u,  v,  g1,  g2,  m,  1, sn,  rs,  B, B, B},
      		{ut, vt, g1t, g2t, mt, 1, snt, rst, B, B, B}
      	},
     0, branch="stopt=0";
     	Switch[uba,
      	1, branch="stopt=0;u=1";
      		{
       			{1,  v,  g1,  g2,  m,  1, sn,  rs,  B,     B,      B    },
       			{ut, vt, g1t, g2t, mt, 0, snt, rst, fwdvt, fwdg2t, fwdmt}
       	    },
        0, branch="stopt=0;u=0";
      		Switch[sntb1,
            1, branch="stopt=0;u=0;snt=1";
       			{
        			{0,  v,  g1,  g2,  m,  0, 1, B,   B,     B,      B    },
        			{ut, vt, g1t, g2t, mt, 0, 1, rst, fwdvt, fwdg2t, fwdmt}
        	    },
       		0, branch="stopt=0;u=0;snt=0";
       			{
        			{0,  v,  g1,  g2,  m,  0, 0, B,   B,     B,      B    },
        			{ut, vt, g1t, g2t, mt, 0, 0, rst, fwdvt, fwdg2t, fwdmt}
        	    },
       		B, branch="stopt=0;u=0;snt=B";
       			{
        			{0,   v,  g1,  g2,  m, 0, 0,   B,    B,      B,      B},
        			{ut, vt, g1t, g2t, mt, 0, B, rst, fwdvt, fwdg2t, fwdmt}
        	                 }
       		],
      	B, branch="stopt=0;u=B";
      		{
       			{0,   v,  g1,  g2,  m, 0, 0,   B,     B,      B,     B},
       			{ut, vt, g1t, g2t, mt, 0, B, rst, fwdvt, fwdg2t, fwdmt}
       		}
      	],
     B, branch="stopt=B";
     	Switch[sntb2,
         1, branch="stopt=B;snt=1";
      		{
	       		{u,  v,  g1,  g2,  m,  0, 1, B,   B,     B,      B    },
    	   		{ut, vt, g1t, g2t, mt, B, 1, rst, fwdvt, fwdg2t, fwdmt}
       		},
      	 0, branch="stopt=B;snt=0";
      		Switch[rst,
                1, branch="stopt=B;snt=0;rst=1";
       				Switch[vt,
        					1, vt1 = 1; vt2 = 1,
        					0, vt1 = 0; vt2 = 0,
        					B, vt1 = B; vt2 = B];
       				Switch[mt,
        					1, mt1 = 1; mt2 = 1,
        					0, mt1 = 0; mt2 = 0,
        					B, mt1 = B; mt2 = B];
       				Switch[g2t,
        					1, g2t1 = 1; g2t2 = 1,
        					0, g2t1 = 0; g2t2 = 0,
        					B, g2t1 = B; g2t2 = B];
       				{
        				{u,  fwdvt,  g1,  fwdg2t, fwdmt, B, 0, 1,   v,     g2,   m},
        				{ut, vt,    g1t,     g2t, mt, B, 0, 1, vt2, fwdg2t, fwdmt}
        			},
       			0, branch="stopt=B;snt=0;rst=0";
       				Switch[vt,
        					1, vt1 = 1; vt2 = 1,
        					0, vt1 = 0; vt2 = 0,
        					B, vt1 = B; vt2 = B];
       				Switch[m,
        					1, me1 = 1; me2 = 1,
        					0, me1 = 0; me2 = 0,
        					B, me1 = B; me2 = B];
       				Switch[mt,
        					1, mt1 = 1; mt2 = 1,
        					0, mt1 = 0; mt2 = 0,
        					B, mt1 = B; mt2 = B];
       				Switch[g2t,
        					1, g2t1 = 1; g2t2 = 1,
        					0, g2t1 = 0; g2t2 = 0,
        					B, g2t1 = B; g2t2 = B];
       				{
        				{u,  fwdvt, TFAXor[g1,me1], B, fwdmt, B, 0, 0, v,     g2,     me2  },
        				{ut, vt, g1t,            fwdg2t, mt, B, 0, 0, fwdvt, fwdg2t, fwdmt}
        			},
       			B, branch="stopt=B;snt=0;rst=B";
       				{
        				{1,  fwdvt,  g1,  fwdg2t,  fwdmt,  0, 0, B, v,     g2,      m   },
        				{ut, vt,     g1t, g2t,     mt,     B, 0, B, fwdvt, fwdg2t, fwdmt}
        			}
       	    ],
        B, branch="stopt=B;snt=B";
      		Switch[ubb,
                1, branch="stopt=B;snt=B;u=1";
       				Switch[vt,
        					1, vt1 = 1; vt2 = 1,
        					0, vt1 = 0; vt2 = 0,
        					B, vt1 = B; vt2 = B];
       				Switch[mt,
        					1, mt1 = 1; mt2 = 1,
        					0, mt1 = 0; mt2 = 0,
        					B, mt1 = B; mt2 = B];
       				Switch[g2t,
        					1, g2t1 = 1; g2t2 = 1,
        					0, g2t1 = 0; g2t2 = 0,
        					B, g2t1 = B; g2t2 = B];
(*      {
            {u,  vt1, g1,  g2t1, mt1, B, 0, 1, v,     g2,     m    },
            {ut, vt2, g1t, g2t2, mt2, B, 0, 1, fwdvt, fwdg2t, fwdmt}
        }
*)
{
{1,  v, g1,  g2, m, 0, 0, B, v,     g2,     m},
{ut, vt2, g1t, g2t2, mt2, B, B, rst, fwdvt, fwdg2t, fwdmt}
}
,
       			0, branch="stopt=B;snt=B;u=0";
       				Switch[gb,
                            1, branch="stopt=B;snt=B;u=0;g1=1";
        						Switch[m,
         							1, me1 = 1; me2 = 1,
         							0, me1 = 0; me2 = 0,
         							B, me1 = B; me2 = B];
        				        {
         							{0,  fwdvt,  TFAXor[g1 , me2], fwdg2t, fwdmt,  B, 0, 0,   v,     g2,     me2  },
         					 		{ut, vt,     g1t,              g2t,    fwdmt,  B, B, rst, fwdvt, fwdg2t, fwdmt}
         						},
        					0,  branch="stopt=B;snt=B;u=0;g1=0";
        						{
         						{0, fwdvt, 0, fwdg2t, fwdmt, B, 0, 1, v, g2, m},
         					 	{ut, vt, g1t, g2t, fwdmt, B, B, rst, fwdvt, fwdg2t, fwdmt}
         						},
        					B,  branch="stopt=B;snt=B;u=0;g1=B";
        						{
         						 {0,  v,   B,  g2,  m, B, B,   B,     B,      B,     B},
         					 	{ut, vt, g1t, g2t, mt, B, B, rst, fwdvt, fwdg2t, fwdmt}
         						}
        					],
       			B, branch="stopt=B;snt=B;u=B";
       				{
        				{B,  v,  B,   g2,  m,  B, B, B,   B,     B,      B    }, 
        				{ut, vt, g1t, g2t, mt, B, B, rst, fwdvt, fwdg2t, fwdmt}
        			}
       		]
    	]
    ];
   
 (* create the state - a triple - to continue *)
Print["case : ",branch];
Print[pair];
   

   {Prepend, pair[[1]], ft[tail, pair[[2]]]}
   
 )
];


FVLastStep[triple_] := Module[
  {
   u, v, g1, g2, m, stop, sn, rs, fwdv, fwdg2, fwdm,
   ut, vt, g1t, g2t, mt, stopt, snt, rst, fwdvt, fwdg2t, fwdmt,
   ft, et,
   uba, ubb, ue,
   gb, ge,
   mt1, mt2,
   me1, me2,
   sntb1, sntb2,
   vt1, vt2,
   g2t1, g2t2,
   tail, pair,
   return},
  (
   (*Print["in1 : ",element];*)
   Print["last step input : ", triple];
   
   (* unpacking the state pair *)
   
   ft = triple[[1]]; (*ft (with linear type of the iterated function) \
   					implements the non-size-increasing mechanism on Church words
   					and by using Mathematica's Fold function on lists
   					   we do not use ft but we have to grant the complexity 
   						constraint of the step function of Fold*)
   et = triple[[2]];
   
   tail = triple[[3]];
   
   (* et is the vector of bits current at the previous iteration step *)
   
   (* unpacking of et *)
   ut = et[[1]];
   vt = et[[2]];
   g1t = et[[3]];
   g2t = et[[4]];
   mt = et[[5]];
   stopt = et[[6]];
   snt = et[[7]];
   rst = et[[8]];
   fwdvt = et[[9]];
   fwdg2t = et[[10]];
   fwdmt = et[[11]];
   
   
   
   return=Switch[stopt,
    1,	branch="stopt=1"; ft[tail, {ut, vt, g1t, g2t, mt, 1, B, B, B, B, B}],
    0,  branch="stopt=0";
    	Switch[snt,
                1, branch="stopt=0;snt=1;"; ft[tail, {ut, vt, g1t, g2t, mt, 0, 1, B, B, B, B}],
                0, branch="stopt=0;snt=0;"; ft[tail, {ut, vt, g1t, g2t, mt, 1, B, B, B, B, B}],
                B, branch="stopt=0;snt=B;"; ft[tail, {ut, vt, g1t, g2t, mt, 0, B, B, B, B, B}]
        ],
    B, branch="stopt=B;";
(*
Switch[rst,
            1, ft[
                ft[tail,  {ut, vt,    g1t,     fwdg2t,    fwdmt, B,  snt, 1, fwdvt, fwdg2t, fwdmt}],
                          {1,  fwdvt,   0,     fwdg2t,    fwdmt, B,    B, 1,     B,      B,     B}],
            0, ft[
                ft[tail,  {ut, vt,    g1t,     fwdg2t,    fwdmt, B,  snt, 0, fwdvt, fwdg2t, fwdmt}],
                          {0,  fwdvt,   0,     fwdg2t,    fwdmt, B,    B, 0,     B,      B,     B}],
*)
        Switch[rst,
            1, branch="stopt=B;rst=1;";
               ft[
                ft[tail,  {ut, vt,       g1t,     fwdg2t,    mt, B,  snt, 1, fwdvt, fwdg2t, fwdmt}],
                          {0,  fwdvt,      0,     fwdg2t,    fwdmt, B,    B, 1,     B,      B,     B}],
            0, branch="stopt=B;rst=0;";
                ft[
                 ft[tail, {ut, vt,       g1t,     fwdg2t,    mt, B,  snt, 0, fwdvt, fwdg2t, fwdmt}],
                          {0,  fwdvt,      0,     fwdg2t,    fwdmt, B,    B, 0,     B,      B,     B}],
            B, branch="stopt=B;rst=0;";
                ft[tail,  {ut, vt, g1t, g2t, mt, B, B, B, B, B, B}]
     ]
];
Print["branch = ",branch];
Print["out    = ",return];

return
   )
  ];


(* first example *)
(*
U = {0, 1, 0, 0}

baseinput = {U,
  {1, 0, 1, 1},
  {0, 0, 0, 1},
  {0, 0, 0, 0},
  {1, 0, 1, 1},
  {0, 0, 0, 0},
  {B, B, B, B},
  {B, B, B, B},
  {0, 0, 0, 0},
  {0, 0, 0, 0},
  {0, 0, 0, 0}
  }

base = MapThread[List, baseinput]; TableForm@base
*)

FVBase = {#1 &, {B, B, B, B, B, B, B, B, B, B, B}, {}}
BVBase = {#1 &, {B, B, B, B, B, B, B, B, B, B, B}, {}}

ForwardVisit = Function[tw, FVLastStep@Fold[FVStep, FVBase, tw]];
BackwardVisit = Function[tw, BVLastStep@Fold[BVStep, BVBase, tw]];

wRevInitBase = {};
wRevInitStep[tail_, element_] :=
Module[{u, v, g1, g2, m, stop, sn, rs, fwdv, fwdg2, fwdm},
(
u = element[[1]];
v = element[[2]];
g1 = element[[3]];
g2 = element[[4]];
m = element[[5]];
stop = element[[6]];
sn = element[[7]];
rs = element[[8]];
fwdv = element[[9]];
fwdg2 = element[[10]];
fwdm = element[[11]];


Prepend[tail, { u, v, g1, g2, m, stop, B, B, 0, 0, 0}]

)]

wRevInit = Function[tw, Fold[wRevInitStep, wRevInitBase, tw]];


wProj = Function[{threadedword}, Fold[ Append[#1, #2[[3]]] &, {}, threadedword]];
StepD = Function[{threadedword}, wRevInit@BackwardVisit@ForwardVisit@Reverse@threadedword];
wInv  = Function[{U, p, sdegree}, wProj@Nest[ StepD, MapThread[List, baseinput[U, p]], sdegree] ];


(*
TableForm@(X1=ForwardVisit[Reverse[base]])
TableForm@(X2=BackwardVisit[Reverse[X1]])
*)





