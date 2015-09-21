
# Ատրիբուտներով քերականություններ և սեմանտիկաներ

Ատրիբուտներով քերականություններում առանձին կառուցվածքներին՝ ոչ տերմինալային սիմվոլներին, համադրված են որոշակի ատրիբուտներ։ Սիմվոլները պարամետրիզացված են և ներկայացնում են տարբերակների ամբողջ դասեր։ Սա թուլ է տալիս պարզեցնել շարահյուսությունը, իսկ գործնականում հնարավորություն է տալիս շարահյուսական անալիզատորը դարձնել իրական թարգմանիչ (Rechenberg and Mössenböck, 1985)։ Թարգմանության պրոցեսը բնորոշվում է ամեն մի ճանաչված սենտենցիալ կառուցվածքին մի որևէ արդյունքի (միգուցե դատարկ) համապատասխանեցմամբ։ Ամեն մի շարահյուսական հավասարումն ուղեկցվում է լրացուցիչ կանոններով, որոնք հարաբերություններ են սահմանում կրճատված սիմվոլների ատրիբուտային արժեքների, ստացված ոչ տերմինալային սիմվոլների ատրիբուտային արժեքների և արդյունքի միջև։ Ստորև առաջարկում ենք ատրիբուտների և ատրիբուտային կանոնների երեք կիրառություններ։


## Կանոններ տիպերի համար

Որպես պարզ օրինակ կդիտարկենք մի քանի տվյալների տիպ ունեցող մի լեզու։ Արտահայտությունների ամեն մի տիպի համար առանձին շարահյուսական կանոն նկարագրելու փոխարեն (ինչպես դա արված էր Algol-60 լեզվում), արտահայտությունները կսահմանենք ճիշտ մեկ անգամ, և նրանում մասնակցող կառուցվածքներին որպես ատրիբուտ կկցենք տվյանների `T` տիպը։ Օրինակ, `T` տիպի արտահայտությունը գրվում է `exp(T)`, այսինքն՝ `exp`-ը ունի `T` ատրիբուտը։ Ըստ այդմ՝ տիպերի համատեղելիության կանոնները դիտարկվում են որպես շարահյուսական կանոնների լրացումներ։ {??} Օրինակ, այն պահանջը, որ գումարման և հանման գործողությունների երկու օպերանդներն էլ պետք է նույն տիպն ունենան, և արդյունքն էլ պետք է ունենա օպերանդների տիպը, տրված են այդիպիսի լրացուցիչ ատրիբուտային կանոններով.

````
Syntax                       Attribute rule  Context condition
exp(T0) =  term(T1)      |   T0 := T1
    exp(T1) "+" term(T2) |   T0 := T1        T1 = T2
    exp(T1) "-" term(T2).    T0 := T1        T1 = T2
````

Եթե `INTEGER` և `REAL` տիպերի օպերանդները պետք է թույլատրվեն խառն արտահայտություններում, ապա կանոններն ավելի մեղմ, բայց միևնույն ժամանակ ավելի բարդ են դառնում.

````
T0 := if (T1 = INTEGER) & (T2 = INTEGER) then INTEGER else REAL,

T1 = INTEGER  or  T1 = REAL
T2 = INTEGER  or  T2 = REAL
````

Ըստ էության, տիպերի համատեղելիության կանոնները նույնպես հաստատուն են այն իմաստով, որ դրանք կարող են ստուգվել առանց ծրագիրը կատարելու։ Այդ պատճառով էլ դրանց առանձնացումը մաքուր շարահյուսկան կանոններից դառնում է անիմաստ, սակայն ատրիբուտային կանոնների տեսքով դրանց միավորումը շարահյուսության հետ լրիվ արդարացված է։ Սակայն նկատենք, որ ատրիբուտային քերականությունները նոր տեսք {?} են ստանում, երբ ատրիբուտի հնարավոր արժեքները (այստեղ՝ տիպերը) և նրանց քանակները նախապես հայտնի չեն։ 

Եթե շարահյուսական հավասարությունը կրկնության կառուցվածք է պարունակում, ապա, ատրիբուտային կանոնների տեսակետից, հարմար կլինի դա արտահայտել ռեկուրսիայի օգնությամբ։ {??} Ոչ պարտադիրության կառուցվածքի առկայության դեպքում ավելի լավ է երկու դեպքերն արտահայտել իրարից առանձին։ Դա ցույց է տրված հետևյալ օրինակում. 

````
exp(T0) = term(T1) {"+" term(T2)}.   exp(T0) = ["-"] term(T1).
````

որտեղ արտահայտություններից ամեն մեկը տրոհված է կանոնների զույգի. 

````
exp(T0) =  term(T1) |                  exp(T0) =  term(T1) |
           exp(T1) "+" term(T2).              "-" term(T1).
````

Արտածման հետ համադրված տիպի կանոններն աշխատում են այն ժամանակ, երբ ճանաչվում է այդ արտածմանը համապատասխանող կառուցվածքը։ Այս համադրումը հեշտ է իրականացնել ռեկուրսիվ վայրէջքի եղանակով գրված անալիզատորներում. ատրիբուտային կանոններն իրականացնող հրամանները պարզապես ներդրվում են վերլուծությունն իրականացնող հրամանների մեջ, իսկ ատրիբուտները ձևակերպվում են որպես շարահյուսական կառուցվածքների (ոչ տերմինալային սիմվոլների) վերլուծության համար գրված պրոցեդուրաների պարամետրեր։ Արտահայտությունները ճանաչող պրոցեդուրան կարող է առաջին օրինակ ծառայել այդ ընդլայնումը ցուցադրելու համար, որտեղ սկզբնական վերլուծող պրոցեդուրան ծառայում է որպես կմաղք. {??}

````
PROCEDURE expression;
BEGIN term;
  WHILE (sym = "+") OR (sym = "-") DO
    GetSym; term
  END
END expression
````

Այս պրոցեդուրան ընդլայնվել է ատրիբուտային կանոններով.

````
PROCEDURE expression(VAR typ0: Type);
  VAR typ1, typ2: Type;
BEGIN term(typ1);
  WHILE (sym = "+") OR (sym = "-") DO
    GetSym; term(typ2);
    typ1 := ResType(typ1, typ2)
  END ;
  typ0 := typ1
END expression
````


## Կանոններ հաշվարկների համար

Որպես երկրորդ օրինակ դիտարկենք օպերանդներում միայն թվեր ունեցող արտահայտություններից կազմված լեզու, որի գործակիցները միայն թվեր են։ Դա մի փոքր քայլ է, որը շարահյուսական անալիզատորը  It is a short step to extend the parser into a program not only recognizing, but at the same time also evaluating expressions. We associate with each construct its value through an attribute called val. In analogy to the type compatibility rules in our previous example, we now must process evaluation rules while parsing. Thereby we have implicitly introduced the notion of semantics:

Շարահյուսություն 			Ատրիբուտային կանոն (սեմանտիկա)

exp(v0)	=	term(v1) |	v0 := v1
		exp(v1) "+" term(v2) |	v0 := v1 + v2
		exp(v1) "-" term(v2).	v0 := v1 - v2
term(v0)	=	factor(v1) |	v0 := v1
		term(v1) "*" factor(v2) |	v0 := v1 * v2
		term(v1) "/" factor(v2).	v0 := v1 / v2
factor(v0)	=	number(v1) |	v0 := v1
		"(" exp(v1) ")".	v0 := v1

Այստեղ ատրիբուտը ճանաչված կառուցվածքի հաշվարկված, թվային արժեքն է։ The necessary extension of the corresponding parsing procedure leads to the following procedure for expressions:

````
PROCEDURE expression(VAR val0: INTEGER);
  VAR val1, val2: INTEGER; op: CHAR;
BEGIN term(val1);
  WHILE (sym = "+") OR (sym = "-") DO
    op : = sym; GetSym; term(val2);
    IF op = "+" THEN val1 : = val1 + val2  ELSE val1 := val1 - val2 END
  END;
  val0 := val1
END expression
````


## Կանոններ թարգմանության համար

A third example of the application of attributed grammars exhibits the basic structure of a compiler. The additional rules associated with a production here do not govern attributes of symbols, but specify the output (code) issued when the production is applied in the parsing process. The generation of output may be considered as a side-effect of parsing. Typically, the output is a sequence of instructions. In this example, the instructions are replaced by abstract symbols, and their output is specified by the operator put.

Syntax		Output rule (semantics)

exp	=	term	-
		exp "+" term	put("+")
		exp "-" term.	put("-")
term	=	factor	-
		term "*" factor	put("*")
		term "/" factor.	put("/")
factor	=	number	put(number)
		"(" exp ")".	-

As can easily be verified, the sequence of output symbols corresponds to the parsed expression in postfix notation. The parser has been extended into a translator.

Infix notation	Postfix notation
2 + 3	2 3 +
2 * 3 + 4	2 3 * 4 +
2 + 3 * 4	2 3 4 * +
(5 - 4) * (3 + 2)	5 4 - 3 2 + *

The procedure parsing and translating expressions is as follows:

PROCEDURE expression;
	VAR op: CHAR;
BEGIN term;
	WHILE (sym = "+") OR (sym = "-") DO
		op := sym; GetSym; term; put(op)
	END
END expression

When using a table-driven parser, the tables expressing the syntax may easily be extended also to represent the attribute rules. If the evaluation and translation rules are also contained in associated tables, one is tempted to speak about a formal definition of the language. The general, table-driven parser grows into a general, table-driven compiler. This, however, has so far remained a utopia, but the idea goes back to the 1960s. It is represented schematically by Figure 5.1.

Figure 5.1. Schema of a general, parametrized compiler.

Ultimately, the basic idea behind every language is that it should serve as a means for communication. This means that partners must use and understand the same language. Promoting the ease by which a language can be modified and extended may therefore be rather counterproductive. Nevertheless, it has become customary to build compilers using table-driven parsers, and to derive these tables from the syntax automatically with the help of tools. The semantics are expressed by procedures whose calls are also integrated automatically into the parser. Compilers thereby not only become bulkier and less efficient than is warranted, but also much less transparent. The latter property remains one of our principal concerns, and therefore we shall not pursue this course any further.


5.4. Վարժություն

5.1. Extend the program for syntactic analysis of EBNF texts in such a way that it generates (1) a list of terminal symbols, (2) a list of nonterminal symbols, and (3) for each nonterminal symbol the sets of its start and follow symbols. Based on these sets, the program is then to determine whether the given syntax can be parsed top-down with a lookahead of a single symbol. If this is not so, the program displays the conflicting productions in a suitable way.
Hint: Use Warshall's algorithm (R. W. Floyd, Algorithm 96, Comm. ACM, June 1962).
TYPE matrix = ARRAY [1..n],[1..n] OF BOOLEAN;
PROCEDURE ancestor(VAR m: matrix; n: INTEGER);
(* Initially m[i,j] is TRUE, if individual i is a parent of individual j.
	At completion, m[i,j] is TRUE, if i is an ancestor of j *)
	VAR i, j, k: INTEGER;
BEGIN
	FOR i := 1 TO n DO
		FOR j := 1 TO n DO
			IF m[j, i] THEN
				FOR k := 1 TO n DO
					IF m[i, k] THEN m[j, k] := TRUE END
				END
			END
		END
	END
END ancestor
It may be assumed that the numbers of terminal and nonterminal symbols of the analysed languages do not exceed a given limit (for example, 32). 
