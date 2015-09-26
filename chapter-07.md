
# Oberon-0 լեզվի շարահյուսական վերլուծությունը

## Բառային վերլուծություն

Մինչ շարահյուսական վերլուծիչի մշակումը սկսելը ուշադրություն դարձնենք նրա բառային վերլուծիչին։ Այն պետք է սկզբնային տեքստում ճանաչի տերմինալային սիմվոլները։ Նախ՝ թվարկենք լեզվի բառարանը (բառապաշարը)։

````
* DIV MOD & + - OR
= # < <= > >= . , : ) ]
OF THEN DO UNTIL ( [ ~ := ;
END ELSE ELSIF IF WHILE REPEAT
ARRAY RECORD CONST TYPE VAR PROCEDURE BEGIN MODULE
````

Մեծատառերով գրված բառերը ինքնուրույն միավորներ են՝ տերմինալային սիմվոլներ, դրանք կոչվում են _պահեստավորված բառեր_։ Դրանք պետք է ճանաչվեն բառային վերլուծիչի կողմից և չեն կարող օգտագործվել որպես իդենտիֆիկատորներ։ Ի լրումն թվարկված սիմվոլների, իդենտիֆիկատորներն ու թվերը նույնպես համարվում են տերմինալային սիմվոլներ։ Այսինքն՝ բառային վերլուծիչը պատասխանատու է նաև իդենտիֆիկատորները և թվերը ճանաչելու համար։

Նպատակահարմար է բառային վերլուծիչը սահմանել որպես առանձին մոդուլ։ Իսկապես, բառային վերլուծիչները մոդուլի գաղափարի օգտագործման դասական օրինակներ են։ Մոդուլը հնարավորություն է տալիս օգտագործողից՝ շարահյուսական վերլուծիչից, թաքցնել իրականացման մանրամասները և տեսանելի դարձնել (դուրս հանել, to export) միայն այն հատկությունները, որոնք պետք են օգտագործողին։ Օգտագործողին տեսանելի հատկությունները ձևավորում են մոդուլի ինտերֆեյսը։

````oberon
DEFINITION OSS; (*Oberon Subset Scanner*)
  IMPORT Texts;
    CONST IdLen = 16;
      (*symbols*) null = 0; times = 1; div = 3; mod = 4;
      and = 5; plus = 6; minus = 7; or = 8; eql = 9;
      neq = 10; lss = 11; leq = 12; gtr = 13; geq = 14;
      period = 18; int = 21; false = 23; true = 24;
      not = 27; lparen = 28; lbrak = 29;
      ident = 31; if = 32; while = 34;
      repeat = 35;
      comma = 40; colon = 41; becomes = 42; rparen = 44;
      rbrak = 45; then = 47; of = 48; do = 49;
      semicolon = 52; end = 53;
      else = 55; elsif = 56; until = 57;
      array = 60; record = 61; const = 63; type = 64;
      var = 65; procedure = 66; begin = 67; module = 69;
      eof = 70;

  TYPE Ident = ARRAY IdLen OF CHAR;

  VAR val: INTEGER;
    id: Ident;
    error: BOOLEAN;

  PROCEDURE Mark(msg: ARRAY OF CHAR);
  PROCEDURE Get(VAR sym: INTEGER);
  PROCEDURE Init(T: Texts.Text; pos: LONGINT);
END OSS.
````

Սիմվոլներն արտապատկերվում են ամբողջ թվերի։ Արտապատկերումը կազմակերպված է հաստատունների բազմություն սահմանելով։ `Mark` պրոցեդուրան ծառայում է ծրագրի տեքստում հայտնաբերված սխալների մասին հաղորդագրություններ արտածելու համար։ Սովորաբար հայտնաբերված սխալի և նրա դիրքի մասին կարճ հաղորդագրություն է գրանցվում {?}֊ում։ `Get` պրոցեդուրան բուն բառային վերլուծիչն է։ Ամեն մի կանչի ժամանակ այն վերադարձնում է հերթական ճանաչած սիմվոլը։ Այդ պրոցեդուրան կատարում է հետևյալ գործողությունները․

1. Բացատներն ու տողի վերջի նիշերն անտեսվում են։
2. Ճանաչվում են ծառայողական բառերը, ինչպիսիք են `BEGIN`֊ը և `END`֊ը։
3. Տառերի ու թվերի հաջորդականությունները՝ տառով սկսվող, որոնք ծառայողական բառեր չեն, ճանաչվում են որպես իդենտիֆիկատորներ։ `sym` պարամետրին տրվում է `ident` արժեքը, իսկ կարդացած նիշերի հաջորդականությունը վերագրվում է `id` գլոբալ փոփոխականին։
4. Թվանշանների հաջորդականությունները ճանաչվում են որպես թվեր։ The parameter sym is given the value number, and the number itself is assigned to the global variable val.
5. Combinations of special characters, such as := and <=, are recognized as a symbol.
6. Comments, represented by sequences of arbitrary characters beginning with (* and ending with *) are skipped.
7. The symbol null is returned, if the scanner reads an illegal character (such as $ or %). The symbol eof is returned if the end of the text is reached. Neither of these symbols occur in a well-formed program text.

