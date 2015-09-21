
# RISC ճարտարապետությունը որպես նպատակ

Պետք է նշել, որ մինչև այս պահը մեր կոմպիլյատորը կարող էր մշակվել առանց այն նպատակային մեքենայի մասին հիշատակելու, որի համար նա կոդ է գեներացնում։ Բայց, իսկապես, ինչո՞ւ պետք է նպատակային մեքենայի կառուցվածքն ազդի շարահյուսական վերլուծության և սխալների մշակման վրա։ Ընդհակառակն, այդպիսի ազդեցությունից պետք է գիտկցաբար խուսափել։ Որպես արդյունք, ըստ քայլ առ քայլ նախագծման սկզբունքի, կամայական համակարգչի համար նախատեսված կոդի գեներատորը կարելի է ավելացնել արդեն գոյություն ունեցող և մեքենայից անկախ վերլուծիչին, որը կատարում է կարկասի դեր։ {??} Սակայն մինչև այս խնդրին ձեռնամուխ լինելը պետք է ընտրել նպատակային ճարտարապետությունը։

Որպեսզի պահպանենք կոմպիլյատորի պարզությունը և ազատ լինենք մշակման To keep both the resulting compiler reasonably simple and the development clear of details that are of relevance only for a specific machine and its idiosyncrasies, we postulate an architecture according to our own choice. Այդպիսով ստանում ենք նշանակալի առավելություն նրանում, որ այն կարող է հարմարեցվել սկզբնական լեզվի պահանջներին։ Այս ճարտարապետությունը գոյություն չունի որպես իրական մեքենա, իրականացված *վերածրագրավորվող տրամաբանական տարրերի զանգվածի* (FPGA - field-programmable gate array) համար, այն ամենայն մանրամասնությամբ նկարագրված որպես Verilog սարքակազմի նկարագրման լեզվի տեքստ։ Բայց այն նաև նկարագրված է *էմուլյատոր* կոչվող ծրագրով։ Իրական համկարգիչը կարող է օգտագործվել այդ ծրագիրը կատարելու համար, հանդես գալով որպես գեներացված կոդը ինտերպրետացնող վիրտուալ մեքենա։

It is not the aim of this text to present the motivations for our choice of the specific virtual architecture with all its details. This chapter is rather intended to serve as a descriptive manual consisting of an informal introduction and a semi-formal definition of the computer in the form of the interpretive program. Էմուլյատորը կարելի է օգտագործել այն դեպքերում, երբ իրական համակարգիչը մատչելի չէ։

Այս համակարգիչը սահմանելիս հատուկ հետևել ենք RISC ճարտարապետությունների մոտիկ գծին։ RISC հապավումը նշանակում է *reduced instruction set computer* — *կրճատված հրահանգների բազմությամբ համակարգիչ*, որտեղ «կրճատված» բառը պետք է հասկանալ բարդ հրահանգների մեծ բազմությամբ համակարգիչների համադրությաբ, as these were dominant until about 1980. Հասկանալի է, որ սա ո՛չ RISC ճարտարապետության էությունը նկարագրելու տեղն է, ո՛չ էլ նրա տարբեր առավելությունները նկարագրելու տեղը։ Here it is attractive because of its simplicity and clarity of concepts, which simplify the description of the instruction set and the choice of instruction sequences corresponding to specific language constructs. The architecture chosen here is similar to the one presented by Hennessy and Patterson (1990) under the name DLX. The small deviations are due to our desire for increased regularity. Among commercial products, the MIPS and ARM architectures are closest to ours.


Ռեսուրսներ և ռեգիստրներ

Ճարտարապետությունը սահմանում է համակարգչի այն առանձնահատկությունները, որոնք կարևոր են ծրագրավորողի և կոմպիլյատոր նախագծողի համար։ Համակարգիչը բաղկացած է թվաբանական սարքից, ղեկավարող սարքից և հիշողությունից։ Մեր թվաբանական սարքը պարունակում է 16 ռեգիստրներ՝ `R0` - `R15`, ամեն մեկը 32 բիթ չափով։ Ղեկավարող սարքը բաղկացած է հրահանգների ռեգիստրից (IR), որը ցույց է տալիս տվյալ պահին կատարվող հրահանգը, և հրահանգների հաչվիչից (PC), որը պարունակում է հաջորդ կատարվող հրահանգի հասցեն (Նկ. 9.1)։ Պրոցեդուրաներին անցման հրահանգներև ոչ բացահայտ եղանակով R15 ռեգիստրն օգտագործում են վերադարձի հասցեն պահելու համար։ Սա այն միակ բացառությունն է այն կանոնից, թե ոլոր ռեգիստրներն օգտագործվում են միատեսակորեն։

Հիշողությունը բաղկացած է 32 բոթանոց բառերից և հասցեավորվում է ըստ բայթերի. այնսինքն՝ բառերի հասցեները 4-ի պատիկ են։ Բացի այդ կան նաև 4 հատ մեկ բիթանոց վիճակի ռեգիստրներ՝ `N`, `Z`, `C` և `V`, որ կոչվում են պայմանական կոդեր։
 
 
Նկար 9.1։ RISC ճարտարապետության բլոկ-սխեման

Կան հրահանգների և դրանց ձևաչափերի երեք տիպ։ Ռեգիստրային հրահանգները աշխատում են միայն ռեգիստրների հետ և տվյալները փոխանակում են թվաբանա-տրամաբանական սարքի (arithmetic-logic unit - ALU) կամ shifter-ի միջոցով։ Հիշողության հրահանգները տվյալները տեղափոխում են ռեգիստրներից հիշողություն և հակառակը։ Անցման հրահանգները փոխում են հրահանգների հաշվիչը։


1. Ռեգիստրային հրահանգներ

Սրանք ունեն երկու տարբեր ձևաչափ։ F0 ձևաչափում օպերանդները `R.b`-ն և `R.c`-ն են։ F1 ձևաչափում երկրորդ օպերանդը ոչ թե ռեգիստր է, այլ `im` հաստատունը։ Երկու ձևաչափում էլ արդյունքը վերագրվում է `R.a` ռեգիստրին։
 
Նկար 9.2. Ռեգիստրային հրահանգների F0 և F1 ձևաչափերը։

Առաջարկվող հրահանգներն են.

````
0   MOV a, c     R.a := R.c	MOV	a, im	R.a := im 
1   AND a, b, c  R.a := R.b & R.c	AND	a, b, im	R.a := R.b & im 
2   OR  a, b, c  R.a := R.b | R.c	OR	a, b, im	R.a := R.b | im 
3   XOR a, b, c  R.a := R.b ^ R.c	XOR	a, b, im	R.a := R.b ^ im
4   LSL a, b, c  R.a := LeftShift(R.b, R.c)  LSL a, b, im R.a := LeftShift(R.b, im)
5   ASR	a, b, c	R.a := RightShift(R.b, R.c)	ASR	a, b, im	R.a := RightShift(R.b, im)

8   ADD	a, b, c	R.a := R.b + R.c	ADD	a, b, im	R.a := R.b + im 
9   SUB	a, b, c	R.a := R.b – R.c	SUB	a, b, im	R.a := R.b - im 
10  MUL	a, b, c	R.a := R.a + R.b	MUL	a, b, im	R.a := R.a + R.b
11  DIV	a, b, c	R.a := R.b DIV R.c	DIV	a, b, im	R.a := R.b DIV im 
12  CMP	b, c	R.b – R.c	CMP	b, im	R.b - im
````

LSL տեղաշարժի գործողությունը տեղաշարժում է դեպի ձախ և աջ կողմից ազատված դիրքերը լրացնում է զրոներով։ Մյուս տեղաշարժի գործողությունը տեղածարժում է դեպի աջ, ինչպես նաև տարածում է նշանի բիթը (arithmetic shift, ASR), եթե ձևափոխության `u` բիթը `0` է, կամ պտտում է բոլոր 32 բիթերը, եթե `u = 1` (rotate, ROR)։ {???}

`im` դաշտի երկարությունը միայն 16 բիթ է։ Այն ընդլայնվում է 32 բիթանոց բառի՝ ըստ `v` ձևափոխության բիթի.

v = 0 ընդլայնել 16 զրոներով  
v = 1 ընդլայնել 16 մեկերով  

Չորս մեկ բիթանոց պայմանական ռեգիստրները փոփոխվում են հետևյալ կերպ։ They are tested by branch instructions.

N : = R.a[31]   (Բացազական)  
Z := (R.a = 0)  (Զրո)  
C := carry out  (գումարման, հանման և համեմատման համար)  
V := overflow   (հշանով գումարման, հանման և համեմատման համար)  


2. Հիշողության հրահանգներ (F2 ձևաչափ)

Կան հիշողությանը դիմող միայն երկու հրահանգներ՝ load և store։ RISC ճարտարապետության համար հատկանշական է, որ հիշողությանը դիմելը չի զուգակցվում այլ գործողությունների հետ։ Բոլոր թվաբանական ու տրամաբանական գործողությունները կատարվում են ռեգիստրների հետ։

````
LD	a, b, off	R.a := Mem[R.b + off] 
ST	a, b, off	Mem[R.b + off] := R.a
````

Fig. 9.3. Հիշողության հրահանգների F2 ձևաչափը

Ձևափոխությունների բիթերն ունեն հետևյալ նշանակությունը.

u = 0: load,  u = 1: store  
v = 0: բառ,   v = 1: բայթ  


3. Ճյուղավորման հրահանգներ (F3 ձևաչափ)

Ճյուղավորման հրահանգներն օգտագործվում են հրահանգների կատարման գծային հաջորդականություն խախտելու համար։ Հաջորդ հրահանգը որոշվում է կամ 24 բիթանոց շեղմամբ, կամ ռեգիստրի արժեքով, depending on the modifier bit u. It indicates the length of the jump forward or backward (PC-relative addressing). Քանի որ հրահանգների երկորությունը միշտ մեկ բառ է, այս շեղումը բառերով է, այլ ոչ թե բայթերով։

Bcond	off  
u = 0	PC := R.c	u = 1	PC := PC+1+off  
v = 0	no link		v = 1	R15 := PC+1  

The modifier v determines, whether the current value of PC be stored in register R15 (the link register). This facility is used for calls to procedures. The value stored is then the return address. The format is shown in Fig. 4.

Fig. 9.4. Ճյուղավորման հրահանգների F3 ձևաչափը

`cond` դաշտը որոշում է, թե ինչ պայմանի դեպքում պետք է ճյուղավորումը կատարվի։ The field cond determines, under which conditions the branch is executed. If not, the instruction has no effect. The selected condition is a logical function of the registers N, Z, C, and V. The following are available:

````
code	cond	condition		code	cond	condition		
0000	MI	negative (minus)	 N	1000	PL	positive (plus)	~N
0001	EQ	equal (zero)	 Z	1001	NE	positive (plus)	~Z
0010	CS	carry set	 C	1010	CC	carry clear	~C
0011	VS	overflow set	 V	1011	VC	overflow clear	~V
0100	LS	less or same	~C|Z	1100	HI	high	~(~C|Z)
0101	LT	less than	NV	1101	GE	greater or equal	~(NV)
0110	LE	less or equal	(NV)|Z	1110	GT	greater than	~((NV)|Z)
0111		always	True	1111		never	False
````

4. Էմուլյատոր

RISC ճարտարապետության էմուլյատորը մի ծրագիր է, որ մոդելավորում է նրա վարքը, կատարում է RISC հրահանգները։ Ստորև ցուցադրված Oberon մոդուլը պարունակում է `Execute` պրոցեդուրան։ Oberon միջավայրում այն կանչվում է `OSG.Execute` հրամանով։ Այս հրամանի առաջին `M` պարամետրը RISC մեքենայի հիշողությունն է, որիմ մեջ կոմպիլյատորը գրառում է կոմպիլյացված հրահանգները։ Անհրաժեշտ են մի քանի դիտողություններ ևս։ The emulator describes only most of the RISC, and a few facilities are omitted.

1.	`C` և `V` պայմանական ռեգիստրները չեն օգտագործվում։ `C` ռեգիստրը պետք է միայն առանց նշանի թվաբանության համար։ `CS`, `CC`, `VS`, `VC`, `LS` և `HI` պայմաններն անտեսվում են (տես աղյուսակը ստորև)։

2.	Հիշողության հրահանգներում բայթով դիմումը նախատեսված չէ։ (`v` բիթն անտեսվում է։) 

3.	Certain addresses are reserved for access to input and output devices. This common technique is called memory mapping. We follow this custom and emulate an input and an output sequence of integersl represented by a scanner S and a writer W. S reads from the text following the command RISC.Execute, and W writes into the Oberon system’s log text. The respective statements are:

	GET(-56, x)	Կարդալ հաջորդ թիվը և վերագրել `x` փոփոխականին,  
	BIT(-52, 0)	The end of the sequence of numbers had been reached.
	PUT(-56, x)	`x` արժեքը գրել գրառումների (log) տեքստում,  
	PUT(-52, 0)	Ավարտել ընթացիկ տողը։  

Oberon-0 լեզվով գրված հետևյալ պարզ ծրագիրը կարդում է ամբողջ թվերի հաջորդականություն և դրանք ուղարկում է արտածման։

````
MODULE TestIO;
    CONST data = -56; ctrl = -52;
    VAR m: INTEGER;
BEGIN GET(data, m);
    WHILE ~BIT(ctrl, 0) DO PUT(data, m); GET(data, m) END ;
    PUT(ctrl, 0)
END TestIO.
````

Ահա էմուլյատորը ներկայացնող Oberen մոդուլը։

````
MODULE RISC;
    IMPORT SYSTEM, Texts, Oberon, OSG;
    CONST MemSize = 1024;    (*in words*)
        MOV = 0; AND = 1; IOR = 2; XOR = 3; LSL = 4; ASR = 5;
        ADD = 8; SUB = 9; MUL = 10; Div = 11; CMP = 12; 
    VAR IR: LONGINT;   (*instruction register*)
        PC: LONGINT;   (*program counter*)
        N, Z: BOOLEAN;  (*condition codes*)
        R: ARRAY 16 OF LONGINT; 
    PROCEDURE Execute(VAR M: ARRAY OF LONGINT; VAR S: Texts.Scanner; VAR W: Texts.Writer)*;
        VAR pq, a, b, op, im: LONGINT;  (*instruction fields*)
            adr, A, B, C: LONGINT;
    BEGIN PC := 0;
        REPEAT (*interpretation cycle*)
            IR := M[PC]; INC(PC);
            pq := IR DIV 40000000H MOD 4;  (*instr. class*, bits 31:30)
            a := IR DIV 1000000H MOD 10H;  (*bits 27:24*)
            b := IR DIV 100000H MOD 10H;   (*bits 23:20*)
            op := IR DIV 10000H MOD 10H;   (*bits 19:16*)
            im := IR MOD 10000H;   (*bits 15:0*)
            CASE pq OF
                0, 1: (*register instructions*)
                    B := R[b];
                    IF pq = 0 THEN C := R[IR MOD 10H]
                    ELSIF ODD(IR DIV 10000000H) THEN C := im + 0FFFF0000H
                    ELSE C := im
                    END ;
                    CASE op OF
                        MOV: A := C |
                        AND: A := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, B) * SYSTEM.VAL(SET,C)) |
                        IOR: A := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, B) + SYSTEM.VAL(SET,C)) |
                        XOR: A := SYSTEM.VAL(LONGINT, SYSTEM.VAL(SET, B) / SYSTEM.VAL(SET,C)) |
                        LSL: A := SYSTEM.LSH(B, C) |
                        ASR: A := ASH(B, C) |
                        ADD: A:= B + C |
                        SUB, CMP: A:= B - C |
                        MUL: A:= B * C |
                        Div: A := B DIV C
                     END ;
                     IF op # CMP THEN R[a] := A END ;
                     N := A < 0; Z := A = 0
            | 2: (*memory instructions*)
                adr := (R[b] + IR) MOD 100000H DIV 4;
                IF adr < MemSize THEN
                    IF ODD(IR DIV 20000000H) THEN M[adr] := R[a] ELSE R[a] := M[adr] END
                ELSE (*I/O*)
                    IF ODD(IR DIV 20000000H) THEN
                        IF adr = 3FFF2H THEN Texts.WriteInt(W, R[a], 8)
                        ELSIF adr = 3FFF3H THEN Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf) 
                        END
                    ELSE 
                        IF adr = 3FFF2H THEN Texts.Scan(S); R[a] := S.i END
                    END
                END ;
            | 3: (*branch instructions*)
                IF (a = 0) & N OR (a = 1) & Z OR (a = 5) & N OR (a = 6) & (N OR Z) OR (a = 7) OR
                        (a = 8) & ~N OR (a = 9) & ~Z OR (a = 13) & ~N OR (a = 14) & ~(N OR Z) THEN
                    IF ODD(IR DIV 10000000H) THEN R[15] := PC*4 END ;
                    IF ODD(IR DIV 20000000H) THEN PC := (PC + (IR MOD 1000000H)) MOD 40000H
                    ELSE PC := R[IR MOD 10H] DIV 4
                    END
                END
            END
        UNTIL PC = 0
    END Execute;
END RISC.
````

This design has been implemented on a single field-programmable gate array (FPGA) and is available on a low-cost Xilinx Spartan-3 development board. It contains a few additional feature not used in the compiler described subsequently and not considered by the emulator listed above. For the sake of completeness we list these additions briefly.

**1. Ռեգիստրային հրահանգներ:** Modifier bit u = 1 has the following consequences:

ADD, SUB	the carry bit C is added (subtracted).  
MUL	the operands are considered as unsigned 32-bit numbers.  
DIV	the result is the remainder (instead of the quotient).  
MOV	the auxiliary H register is accessed. It holds the high-order 32 bits of the product after a multiplication, and the remainder after a division.  

**2. Ընդհատումներ:** An input signal is provided for causing an interrupt. Registers PC and the condition codes are saved, and processing proceeds at location 1 (containing a branch instruction). A branch register instruction with bit IR[4] set then restores PC and the condition codes to their state before the interrupt. There is an additional register intEnb. If reset, interrupts are inhibited. It is set by a branch instruction to IR[7], if IR[6] = 1.
 
