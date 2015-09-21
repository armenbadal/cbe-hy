
# Oberon-0 ծրագրավորման լեզուն

Որպեսզի խուսափենք ընդհանրությունների ու վերացական տեսությունների կորստից, պետք է կառուցենք կոնկրետ կոմպիլյատոր և դրա օրինակով կբացատրենք նախագծման ընթացքում առաջացող տարբեր խնդիրները։ Դա անելու համար պետք է առաջարկենք որոշակի սկսզբնական լեզու։ (???)

Իհարկե, մենք պետք է պահպանենք այս կոմպիլյատորի, ինչպես նաև լեզվի բավականաչափ պարզությունըOf course we must keep this compiler, and therefore also the language, sufficiently simple in order to remain within the scope of an introductory tutorial. On the other hand, we wish to explain as many of the fundamental constructs of languages and compilation techniques as possible. Out of these considerations have grown the boundary conditions for the choice of the language: it must be simple, yet representative. We have chosen a subset of the language Oberon (Reiser and Wirth, 1992), which is a condensation of its ancestors Modula-2 (Wirth, 1982) and Pascal (Wirth, 1971) into their essential features. Oberon may be said to be the latest offspring in the tradition of Algol 60 (Naur, 1960). Our subset is called Oberon-0, and it is sufficiently powerful to teach and exercise the foundations of modern programming methods.

Ծրագրային կառուցվածքի տեսակետից Oberon-0-ն բավականաչափ լավ է մշակված։ Տարրական հրամանը վերագրումն է։ Բաղադրյալ հրամաններն ընդգրկում են հաջորդման, ճյուղավորման և կրկնման հրամանների գաղափարները, {???} վերջիններս որպես IF, WHILE և ՐԵՊԵԱՏ հրամաններ։ Oberon-0-ն պարունակում է նաև ենթածրագրի կարևորագույն գաղափարը՝ ներկայացված պրոցեդուրայի սահմանմամբ և կանչով։ Նրա հզորությունը հենվում է հիմնականում պարամետրիզացված պրոցեդուրաների հնարավորության վրա։ Oberon-ում տարբերակում ենք արժեք-պարամետրերը և փոփոխական-պարամետրերը։

Սակայն ինչ վերաբերում է տվյալների տիպերին, Oberon-0-ն բավականին աղքատ է։ Միակ պրիմիտիվ տվյալների տիպերը ամբողջ թվերն են և տրամաբանական արժեքները, նշանակված որպես INTEGER և BOOLEAN։ It is thus possible to declare integer-valued constants and variables, and to construct expressions with arithmetic operators. Արտահայտությունների համեմատումը բերում է Բուլյան արժեքների, որոնց նկատմամբ կարող են կիրառվել տրամաբանական գործողություններ։

Մատչելի տվյալների կառուցվածքներն են զանգվածը (array) և գրառումը (record)։ Դրանք կարող են լինել կամայականորեն ներդրված։ Ցուցիչները, սակայն, բացակայում են։

Պրոցեդուրաները ներկայացնում են հրամանների ֆունկցիոնալ միավորներ։ Այդ պատճառով էլ նպատակահարմար է անունների լոկալությունը համադրել պրոցեդուրայի հասկացության հետ։ Oberon-0-ն հնարավորություն է տալիս պրոցեդուրայում սահմանել լոկայ իդենտիֆիկատորներ այնպես, որ դրանք վավերական (տեսանելի) են միայն տվյալ պրոցեդուրայում։

This very brief overview of Oberon-0 is primarily to provide the reader with the context necessary to understand the subsequent syntax, defined in terms of EBNF.

````
ident  =  letter {letter | digit}.
integer  =  digit {digit}.
selector  =  {"." ident | "[" expression "]"}.
number  =  integer.
factor  =  ident selector | number | "(" expression ")" | "~" factor.
term  =  factor {("*" | "DIV" | "MOD" | "&") factor}.
SimpleExpression  =  ["+"|"-"] term {("+" | "–" | "OR") term}.
expression  =  SimpleExpression
	[("=" | "#" | "<" | "<=" | ">" | ">=") SimpleExpression].
assignment  =  ident selector ":=" expression.
ActualParameters  =  "(" [expression {"," expression}] ")" .
ProcedureCall  =  ident selector [ActualParameters].
IfStatement  =  "IF" expression "THEN" StatementSequence
	{"ELSIF" expression "THEN" StatementSequence}
	["ELSE" StatementSequence] "END".
WhileStatement  =  "WHILE" expression "DO" StatementSequence "END".
RepeatStatement  =  “REPEAT” Statement Sequence “UNTIL” expression.
statement  =  [assignment | ProcedureCall |
	IfStatement | WhileStatement | RepeatStatement].
StatementSequence  =  statement {";" statement}.
IdentList  =  ident {"," ident}.
ArrayType  =  "ARRAY" expression "OF" type.
FieldList  =  [IdentList ":" type].
RecordType  =  "RECORD" FieldList {";" FieldList} "END".
type  =  ident | ArrayType | RecordType.
FPSection  =  ["VAR"] IdentList ":" type.
FormalParameters  =  "(" [FPSection {";" FPSection}] ")".
ProcedureHeading  =  "PROCEDURE" ident [FormalParameters].
ProcedureBody  =  declarations ["BEGIN" StatementSequence] "END" ident.
ProcedureDeclaration  =  ProcedureHeading ";" ProcedureBody.
declarations  =  ["CONST" {ident "=" expression ";"}]
	["TYPE" {ident "=" type ";"}]
	["VAR" {IdentList ":" type ";"}]
	{ProcedureDeclaration ";"}.
module  =  "MODULE" ident ";" declarations
	["BEGIN" StatementSequence] "END" ident "." .
````

Մոդուլի հետևյալ օրինակն ընթերցողին թույլ կտա հասկանալ լեզվի բնույթը։ Այս մոդուլը պարունակում է մի քանի լավ ծանոթ պրոցեդուրաներ։ Այն նաև պարունակում է `Read` և `Write` հրամանները, որոնց նշանակությունն ակնհայտ է, բայց դրանք շարահյուսությաբ մեջ նկարագրված չեն։

````
MODULE Sample;
PROCEDURE Multiply;
 	VAR x, y, z: INTEGER;
BEGIN Read(x); Read(y); z := 0;
 	WHILE x > 0 DO
 		IF x MOD 2 = 1 THEN z := z + y END ;
		y := 2*y; x := x DIV 2
	END ;
	Write(x); Write(y); Write(z); WriteLn
END Multiply;
````

````
PROCEDURE Divide;
 	VAR x, y, r, q, w: INTEGER;
BEGIN Read(x); Read(y); r := x; q := 0; w := y;
 	WHILE w <= r DO w := 2*w END ;
 	WHILE w > y DO
		q := 2*q; w := w DIV 2;
		IF w <= r THEN r := r - w; q := q + 1 END
	END ;
	Write(x); Write(y); Write(q); Write(r); WriteLn
END Divide;
````

````
PROCEDURE BinSearch;
	VAR i, j, k, n, x: INTEGER;
		a: ARRAY 32 OF INTEGER;
BEGIN Read(n); k := 0;
	WHILE k < n DO Read(a[k]); k := k + 1 END ;
	Read(x); i := 0; j := n;
	WHILE i < j DO
		k := (i+j) DIV 2;
		IF x < a[k] THEN j := k ELSE i := k+1 END
	END ;
	Write(i); Write(j); Write(a[j]); WriteLn
END BinSearch;
END Sample.
````

6.1. Վարժություն

6.1. Determine the code for the computer defined in Chapter 9, generated from the program listed at the end of this Chapter. 

