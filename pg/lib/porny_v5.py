# -*- coding: utf-8 -*-
"""
theporny_fixed_v5.py  --  TVBox Spider (FongMi / 影视仓 / OK影视 / PeekPro 兼容)

站点     : https://theporny.com
协议     : 站点前端是 Angular 壳, 所有业务请求统一走
           POST {网关}/js   体: {"url":"<接口>","app":"theporny.com", ...}
           响应体 {"r":"<base64>"}, base64 里是 OpenSSL "Salted__" 容器,
           口令取自站点前端常量. 本文件用纯 Python 复现该算法:
             key||iv = EVP_BytesToKey(MD5 迭代)  ->  AES-256-CBC  ->  PKCS7  ->  JSON
           网关域名有多个镜像, 脚本自动轮换.
搜索     : 查询参数放在 /js 顶层请求体。英文大小写、简繁字形、番号分隔形式
           统一扩展召回；空格分词后逐词查询并在本地执行 AND。按 vod_id 去重并
           按所有逻辑词的匹配质量排序，分页在 Spider 实例内缓存.
播放     : 详情接口下发带时效签名的 m3u8, 播放时必须重新取一次拿新签名.
           清单里分片是相对路径, 由本脚本自带的 127.0.0.1 中转绝对化后再吐给播放器.
依赖     : 零第三方依赖 (requests 有则用, 无则 urllib 兜底)
兼容     : CPython 2.7 / 3.x / Jython 2.7

ext 用法:
    "https://theporny.com|interval=1.2|img=direct|proxy=1"
    可选项全部可省:
      base=        网关主域名, 默认 v2.cdn199.com
      interval=    请求间隔秒, 默认 1.0 (站点有频控, 别低于 0.5)
      img=         direct(默认) | relay  图片是否走本地中转
      proxy=       1(默认) 播放清单走本地中转  | 0 直接给原始 m3u8
"""

import base64
import binascii
import json
import re
import socket
import threading
import time

try:
    import hashlib
except ImportError:
    hashlib = None

try:
    import requests
except ImportError:
    requests = None

try:
    from urllib.parse import quote, urljoin, unquote
    from urllib.request import Request, urlopen
    from urllib.error import URLError
except ImportError:  # py2
    from urllib import quote, unquote
    from urllib2 import Request, urlopen, URLError
    from urlparse import urljoin

try:
    text_type = unicode  # noqa  py2
except NameError:
    text_type = str


# ---------------------------------------------------------------- 基础工具

def _to_bytes(v):
    if isinstance(v, bytes):
        return v
    if isinstance(v, bytearray):
        return bytes(v)
    if text_type is not str and isinstance(v, text_type):
        return v.encode("utf-8")
    return str(v).encode("utf-8")


def _to_text(v):
    if isinstance(v, text_type):
        return v
    if isinstance(v, (bytes, bytearray)):
        try:
            return v.decode("utf-8")
        except Exception:
            return v.decode("latin-1", "ignore")
    return text_type(v)


def _fold_text(v):
    """兼容 Python 2/3 的不区分大小写文本。"""
    t = _to_text(v or "")
    fn = getattr(t, "casefold", None)
    if fn is not None:
        try:
            return fn()
        except Exception:
            pass
    return t.lower()


def _ascii_alnum(ch):
    return (u"0" <= ch <= u"9" or u"a" <= ch <= u"z" or
            u"A" <= ch <= u"Z")


def _ascii_digit(ch):
    return u"0" <= ch <= u"9"


# 参考 BYVoid/OpenCC：使用官方字符词典扩展简繁搜索召回；Apache-2.0。
# 仅嵌入 BMP 单字符映射；标题不转换，只用于查询变体和本地等价匹配。
_S2T_KEYS = (
    u"㐷㐹㐽㑇㑈㑔㑩㓥㓰㔉㖊㖞㘎㚯㛀㛣㛤㟆㟥㡎㤘㤽㥪㧏㧐㧑㧟㧰㨫㭎㭏㭤㭴㱩㱮㲿㳔㳕㳠㳡㳽㴋㶉㶶㶽㺍㻅䀥䁖䂵䃅䅉䅟䇲䉤䌶䌷䌸䌹䌺䌻䌼䌽䌾䌿䍀䍁䍠䎬䏝䓓䓕䓖䓨䗖䙌䙓䜣䜤䜧䜩䝙䞍䞐䟢䥺䥽䥾䦂䦃䦅䦆䦶䦷䩄䯄䯅䲝䲟䲠䲡䲢䲣䴓䴔䴕䴖䴗䴘䴙䶮万与丑专业丛东丝丢两严丧个丰临为丽举么义乌乐乔习乡书买乱了争于亏云亘亚产亩亲亵亸亿仅仆仇从仑仓仪们价仿众优伙会伛伞伟传伡伣伤伥伦伧伪伫体余佛佣佥侠侣侥侦侧侨侩侪侬侭俊俣俦俨俩俪俫俭修借债倾偬偻偾偿傤傥傧储傩僵儿克兑兖党"
    u"兰关兴具兹养兽冁内冈册写军农冢冬冯冲决况冻净凄准凉凌减凑凛几凤凫凭凯凶出击凿刍划刘则刚创删别刬刭刮制刹刽刾刿剀剂剐剑剥剧劝办务劢动励劲劳势勋勚匀匦匮区医千升华协单卖卜占卢卤卧卫却卷卺厂厅历厉压厌厍厐厕厘厢厣厦厨厩厮县叁参叆叇双发变叙叠只台叶号叹叽吁吃合吊同后向吓吕吗吣吨听启吴呆呐呒呓呕呖呗员呙呛呜周咏咙咛咝咤咨咸咽哄响哑哒哓哔哕哗哙哜哝哟唇唛唝唠唡唢唤啧啬啭啮啯啰啴啸喂喷喽喾嗫嗳嘘嘤嘱噜噪嚣回团园困囱围囵国图圆圣圹场坏坐块坚坛坜坝坞坟坠"
    u"坯垄垅垆垒垦垩垫垭垯垱垲垴埘埙埚堑堕堤塆墙壮声壳壶壸处备复够夫头夸夹夺奁奂奋奖奥奸妆妇妈妩妪妫姗姜姹娄娅娆娇娈娘娱娲娴婳婴婵婶媪媭嫒嫔嫱嬷孙学孪宁它宝实宠审宪宫家宽宾寝对寻导寿将尔尘尝尧尴尸尽局层屃屉届属屡屦屿岁岂岖岗岘岚岛岩岭岳岽岿峃峄峡峣峤峥峦峰崂崃崄崭嵘嵚嵝巅巨巩巯币布帅师帏帐帘帜带帧席帮帱帻帼幂干并幸广庄庆床庐庑库应庙庞废庵庼廪开异弃弑张弥弦弪弯弹强归当录彟彦彨彩彻征径徕御忆忏志忧念忾怀态怂怃怄怅怆怜总怼怿恋恒恤恳恶恸恹恺恻恼恽"
    u"悦悫悬悭悮悯惊惧惨惩惫惬惭惮惯愈愠愤愦愿慑慭懑懒懔戆戋戏戗战戚戬戯户扇才扎扑托扣执扩扪扫扬扰折抚抛抟抠抡抢护报抵担拐拟拢拣拥拦拧拨择拿挂挚挛挜挝挞挟挠挡挢挣挤挥挦挨挽捆捍捝捞损捡换捣据掳掴掷掸掺掼揽揾揿搀搁搂搄搅搜携摄摅摆摇摈摊撄撑撵撷撸撺擜擞攒敌敚敛敩数斋斓斗斤斩斫断旋无旧时旷旸昆昙昵昼昽显晋晒晓晔晕晖暂暗暧曲札术朱朴机杀杂权杆杠条来杨杩杯杰松板极构果枞枢枣枥枧枨枪枫枭柜柠柽栀栅标栈栉栊栋栌栎栏树栖栗样核栾桠桡桢档桤桥桦桧桨桩桪梁梦梼"
    u"梾梿检棁棂棱椁椝椟椠椢椤椫椭椮楼榄榅榇榈榉榝槚槛槟槠横樯樱橥橱橹橼檗檩欢欤欧欲歼殁殇残殒殓殚殡殴毁毂毕毙毡毵氇气氢氩氲汇汉汤汹沄沈沟没沣沤沥沦沧沨沩沪沾泛泞注泪泶泷泸泺泻泼泽泾洁洒洼浃浅浆浇浈浉浊测浍济浏浐浑浒浓浔浕浚涂涌涚涛涝涞涟涠涡涢涣涤润涧涨涩淀渊渌渍渎渐渑渔渖渗温游湾湿溁溃溅溆溇溪滗滚滞滟滠满滢滤滥滦滨滩滪漓潆潇潋潍潜潴澄澛澜濑濒灏灭灯灵灶灾灿炀炉炖炜炝点炼炽烁烂烃烛烟烦烧烨烩烫烬热焕焖焘焰煴熏爱爷牍牦牵牺犊状犷犸犹狈狝狞独狭狮"
    u"狯狰狱狲狸猃猎猕猡猪猫猬献獭玑玙玚玛玩玮环现玱玺珐珑珰珲琅琎琏琐琼瑶瑷瑸璇璎瓒瓮瓯电画畅畴疖疗疟疠疡疬疭疮疯疱疴症痈痉痒痖痨痪痫痴瘅瘆瘗瘘瘪瘫瘾瘿癞癣癫皂皑皱皲盏盐监盖盗盘眍眦眬睁睐睑瞆瞒瞩矩矫矶矾矿砀码砖砗砚砜砺砻砾础硁硕硖硗硙硚确硵硷碍碛碜碱礼祃祎祢祯祷祸禀禄禅离私秃秆秋种秘积称秽秾稆税稣稳穑穗穞穷窃窍窎窑窜窝窥窦窭竖竞笃笋笔笕笺笼笾筑筚筛筜筝筱筹筼签筿简箓箦箧箨箩箪箫篑篓篮篯篱簖籁籴类籼粜粝粤粪粮粽糁糇糊糍系紧累絷緼縆纟纠纡红纣纤"
    u"纥约级纨纩纪纫纬纭纮纯纰纱纲纳纴纵纶纷纸纹纺纻纼纽纾线绀绁绂练组绅细织终绉绊绋绌绍绎经绐绑绒结绔绕绖绗绘给绚绛络绝绞统绠绡绢绣绤绥绦继绨绩绪绫绬续绮绯绰绱绲绳维绵绶绷绸绹绺绻综绽绾绿缀缁缂缃缄缅缆缇缈缉缊缋缌缍缎缏缐缑缒缓缔缕编缗缘缙缚缛缜缝缞缟缠缡缢缣缤缥缦缧缨缩缪缫缬缭缮缯缰缱缲缳缴缵罂网罗罚罢罴羁羟羡群翘翙翚耇耢耧耸耻聂聋职聍联聩聪肃肠肤肮肴肾肿胀胁胄胆背胜胡胧胨胪胫胶脉脍脏脐脑脓脔脚脱脶脸腊腌腘腭腻腼腽腾膑膻臜致舆舍舣舰舱舻艰艳"
    u"艺节芈芗芜芦芸苁苇苈苋苌苍苎苏苔苧苹范茎茏茑茔茕茧荆荐荙荚荛荜荝荞荟荠荡荣荤荥荦荧荨荩荪荫荬荭荮药莅莱莲莳莴莶获莸莹莺莼萚萝萤营萦萧萨葱蒀蒇蒉蒋蒌蒏蒙蓝蓟蓠蓣蓥蓦蔂蔑蔷蔹蔺蔼蕰蕲蕴薮藓藤藴蘖虏虑虚虫虬虮虱虽虾虿蚀蚁蚂蚃蚕蚝蚬蛊蛎蛏蛮蛰蛱蛲蛳蛴蜕蜗蜡蝇蝈蝉蝎蝼蝾螀螨蟏衅衔补表衬衮袄袅袆袜袭袯装裆裈裢裣裤裥褛褴襕见观觃规觅视觇览觉觊觋觌觍觎觏觐觑觞触觯訚詟誉誊讠计订讣认讥讦讧讨让讪讫讬训议讯记讱讲讳讴讵讶讷许讹论讻讼讽设访诀证诂诃评诅识诇诈"
    u"诉诊诋诌词诎诏诐译诒诓诔试诖诗诘诙诚诛诜话诞诟诠诡询诣诤该详诧诨诩诪诫诬语诮误诰诱诲诳说诵诶请诸诹诺读诼诽课诿谀谁谂调谄谅谆谇谈谉谊谋谌谍谎谏谐谑谒谓谔谕谖谗谘谙谚谛谜谝谞谟谠谡谢谣谤谥谦谧谨谩谪谫谬谭谮谯谰谱谲谳谴谵谶谷豆象豮贝贞负贠贡财责贤败账货质贩贪贫贬购贮贯贰贱贲贳贴贵贶贷贸费贺贻贼贽贾贿赀赁赂赃资赅赆赇赈赉赊赋赌赍赎赏赐赑赒赓赔赕赖赗赘赙赚赛赜赝赞赟赠赡赢赣赪赵赶趋趱趸跃跄跖跞践跶跷跸跹跻踌踪踬踯蹑蹒蹰蹿躏躜躯輼车轧轨轩轪轫转"
    u"轭轮软轰轱轲轳轴轵轶轷轸轹轺轻轼载轾轿辀辁辂较辄辅辆辇辈辉辊辋辌辍辎辏辐辑辒输辔辕辖辗辘辙辚辞辟辩辫边辽达迁过迈运还这进远违连迟迩迳迹适选逊递逦逻遗遥邓邝邬邮邹邺邻郁郏郐郑郓郦郧郸酂酝酦酱酸酽酾酿醖采释里鉴銮錾钅钆钇针钉钊钋钌钍钎钏钐钑钒钓钔钕钖钗钘钙钚钛钜钝钞钟钠钡钢钣钤钥钦钧钨钩钪钫钬钭钮钯钰钱钲钳钴钵钶钷钸钹钺钻钼钽钾钿铀铁铂铃铄铅铆铇铈铉铊铋铌铍铎铏铐铑铒铓铔铕铖铗铘铙铚铛铜铝铞铟铠铡铢铣铤铥铦铧铨铩铪铫铬铭铮铯铰铱铲铳铴铵银铷"
    u"铸铹铺铻铼铽链铿销锁锂锃锄锅锆锇锈锉锊锋锌锍锎锏锐锑锒锓锔锕锖锗锘错锚锛锜锝锞锟锠锡锢锣锤锥锦锧锨锩锪锫锬锭键锯锰锱锲锳锴锵锶锷锸锹锺锻锼锽锾锿镀镁镂镃镄镅镆镇镈镉镊镋镌镍镎镏镐镑镒镓镔镕镖镗镘镙镚镛镜镝镞镟镠镡镢镣镤镥镦镧镨镩镪镫镬镭镮镯镰镱镲镳镴镵镶长门闩闪闫闬闭问闯闰闱闲闳间闵闶闷闸闹闺闻闼闽闾闿阀阁阂阃阄阅阆阇阈阉阊阋阌阍阎阏阐阑阒阓阔阕阖阗阘阙阚阛队阳阴阵阶际陆陇陈陉陕陦陧陨险随隐隶隽难雇雏雕雠雳雾霁霉霡霭靓靔静面靥鞑鞒鞯鞲韦"
    u"韧韨韩韪韫韬韵页顶顷顸项顺须顼顽顾顿颀颁颂颃预颅领颇颈颉颊颋颌颍颎颏颐频颒颓颔颕颖颗题颙颚颛颜额颞颟颠颡颢颣颤颥颦颧风飏飐飑飒飓飔飕飖飗飘飙飚飞飨餍饣饤饥饦饧饨饩饪饫饬饭饮饯饰饱饲饳饴饵饶饷饸饹饺饻饼饽饾饿馀馁馂馃馄馅馆馇馈馉馊馋馌馍馎馏馐馑馒馓馔馕马驭驮驯驰驱驲驳驴驵驶驷驸驹驺驻驼驽驾驿骀骁骂骃骄骅骆骇骈骉骊骋验骍骎骏骐骑骒骓骔骕骖骗骘骙骚骛骜骝骞骟骠骡骢骣骤骥骦骧髅髋髌鬓鬶魇魉鱼鱽鱾鱿鲀鲁鲂鲃鲄鲅鲆鲇鲈鲉鲊鲋鲌鲍鲎鲏鲐鲑鲒鲓鲔鲕鲖鲗"
    u"鲘鲙鲚鲛鲜鲝鲞鲟鲠鲡鲢鲣鲤鲥鲦鲧鲨鲩鲪鲫鲬鲭鲮鲯鲰鲱鲲鲳鲴鲵鲶鲷鲸鲹鲺鲻鲼鲽鲾鲿鳀鳁鳂鳃鳄鳅鳆鳇鳈鳉鳊鳋鳌鳍鳎鳏鳐鳑鳒鳓鳔鳕鳖鳗鳘鳙鳚鳛鳜鳝鳞鳟鳠鳡鳢鳣鳤鸟鸠鸡鸢鸣鸤鸥鸦鸧鸨鸩鸪鸫鸬鸭鸮鸯鸰鸱鸲鸳鸴鸵鸶鸷鸸鸹鸺鸻鸼鸽鸾鸿鹀鹁鹂鹃鹄鹅鹆鹇鹈鹉鹊鹋鹌鹍鹎鹏鹐鹑鹒鹓鹔鹕鹖鹗鹘鹙鹚鹛鹜鹝鹞鹟鹠鹡鹢鹣鹤鹥鹦鹧鹨鹩鹪鹫鹬鹭鹮鹯鹰鹱鹲鹳鹴鹾麦麸麹麺麽黄黉黡黩黪黾鼋鼌鼍鼹齐齑齿龀龁龂龃龄龅龆龇龈龉龊龋龌龙龚龛龟鿎鿏鿒鿔"
)
_S2T_VALS = (
    u"傌㑶偑㑳倲㑯儸劏劃劚噚喎㘚㜄媰㜏孋㠏嵾幓㥮懤慺掆㩳撝擓擽㩜棡椲樢樫殰殨瀇濧灡澾濄瀰潚鸂燶煱獱璯䁻瞜碽磾稏穇筴籔䊷紬縳絅䋙䋚綐綵䋻䋹繿繸䍦䎱膞薵薳藭罃螮䙡襬訢鿁䜀讌貙䝼賰躎釾鏺䥱䥇鐯鐥钁䦛䦟靦騧䯀䱽鮣鰆鰌鰧䱷鳾鵁鴷鶄鶪鷉鸊龑萬與醜專業叢東絲丟兩嚴喪個豐臨爲麗舉麼義烏樂喬習鄉書買亂了爭於虧雲亙亞產畝親褻嚲億僅僕仇從侖倉儀們價仿衆優夥會傴傘偉傳俥俔傷倀倫傖僞佇體餘佛傭僉俠侶僥偵側僑儈儕儂儘俊俁儔儼倆儷倈儉修借債傾傯僂僨償儎儻儐儲儺僵兒克兌兗黨"
    u"蘭關興具茲養獸囅內岡冊寫軍農冢冬馮衝決況凍淨悽準涼凌減湊凜幾鳳鳧憑凱兇出擊鑿芻劃劉則剛創刪別剗剄刮制剎劊㓨劌剴劑剮劍剝劇勸辦務勱動勵勁勞勢勳勩勻匭匱區醫千升華協單賣卜佔盧滷臥衛卻卷巹廠廳歷厲壓厭厙龎廁釐廂厴廈廚廄廝縣叄參靉靆雙發變敘疊只臺葉號嘆嘰籲喫合吊同後向嚇呂嗎吣噸聽啓吳呆吶嘸囈嘔嚦唄員咼嗆嗚周詠嚨嚀噝吒諮鹹咽哄響啞噠嘵嗶噦譁噲嚌噥喲脣嘜嗊嘮啢嗩喚嘖嗇囀齧嘓囉嘽嘯喂噴嘍嚳囁噯噓嚶囑嚕噪囂回團園困囪圍圇國圖圓聖壙場壞坐塊堅壇壢壩塢墳墜"
    u"坯壟壠壚壘墾堊墊埡墶壋塏堖塒壎堝塹墮堤壪牆壯聲殼壺壼處備復夠夫頭誇夾奪奩奐奮獎奧奸妝婦媽嫵嫗嬀姍姜奼婁婭嬈嬌孌娘娛媧嫺嫿嬰嬋嬸媼嬃嬡嬪嬙嬤孫學孿寧它寶實寵審憲宮家寬賓寢對尋導壽將爾塵嘗堯尷屍盡局層屓屜屆屬屢屨嶼歲豈嶇崗峴嵐島巖嶺嶽崬巋嶨嶧峽嶢嶠崢巒峯嶗崍嶮嶄嶸嶔嶁巔巨鞏巰幣布帥師幃帳簾幟帶幀席幫幬幘幗冪幹並幸廣莊慶牀廬廡庫應廟龐廢庵廎廩開異棄弒張彌弦弳彎彈強歸當錄彠彥彲彩徹徵徑徠御憶懺志憂念愾懷態慫憮慪悵愴憐總懟懌戀恆恤懇惡慟懨愷惻惱惲"
    u"悅愨懸慳悞憫驚懼慘懲憊愜慚憚慣愈慍憤憒願懾憖懣懶懍戇戔戲戧戰戚戩戱戶扇才扎撲托扣執擴捫掃揚擾折撫拋摶摳掄搶護報抵擔拐擬攏揀擁攔擰撥擇拿掛摯攣掗撾撻挾撓擋撟掙擠揮撏挨挽捆捍挩撈損撿換搗據擄摑擲撣摻摜攬搵撳攙擱摟揯攪搜攜攝攄擺搖擯攤攖撐攆擷擼攛㩵擻攢敵敓斂斆數齋斕鬥斤斬斫斷旋無舊時曠暘昆曇暱晝曨顯晉曬曉曄暈暉暫暗曖曲札術朱樸機殺雜權杆槓條來楊榪杯傑松板極構果樅樞棗櫪梘棖槍楓梟櫃檸檉梔柵標棧櫛櫳棟櫨櫟欄樹棲栗樣核欒椏橈楨檔榿橋樺檜槳樁樳梁夢檮"
    u"棶槤檢梲欞棱槨槼櫝槧槶欏樿橢槮樓欖榲櫬櫚櫸樧檟檻檳櫧橫檣櫻櫫櫥櫓櫞檗檁歡歟歐欲殲歿殤殘殞殮殫殯毆毀轂畢斃氈毿氌氣氫氬氳匯漢湯洶澐沈溝沒灃漚瀝淪滄渢潙滬沾泛濘注淚澩瀧瀘濼瀉潑澤涇潔灑窪浹淺漿澆湞溮濁測澮濟瀏滻渾滸濃潯濜浚塗湧涗濤澇淶漣潿渦溳渙滌潤澗漲澀澱淵淥漬瀆漸澠漁瀋滲溫遊灣溼濚潰濺漵漊溪潷滾滯灩灄滿瀅濾濫灤濱灘澦漓瀠瀟瀲濰潛瀦澄瀂瀾瀨瀕灝滅燈靈竈災燦煬爐燉煒熗點煉熾爍爛烴燭煙煩燒燁燴燙燼熱煥燜燾焰熅燻愛爺牘犛牽犧犢狀獷獁猶狽獮獰獨狹獅"
    u"獪猙獄猻狸獫獵獼玀豬貓蝟獻獺璣璵瑒瑪玩瑋環現瑲璽琺瓏璫琿琅璡璉瑣瓊瑤璦璸璇瓔瓚甕甌電畫暢疇癤療瘧癘瘍癧瘲瘡瘋皰痾症癰痙癢瘂癆瘓癇癡癉瘮瘞瘻癟癱癮癭癩癬癲皁皚皺皸盞鹽監蓋盜盤瞘眥矓睜睞瞼瞶瞞矚矩矯磯礬礦碭碼磚硨硯碸礪礱礫礎硜碩硤磽磑礄確磠硷礙磧磣鹼禮禡禕禰禎禱禍稟祿禪離私禿稈秋種祕積稱穢穠穭稅穌穩穡穗穭窮竊竅窵窯竄窩窺竇窶豎競篤筍筆筧箋籠籩築篳篩簹箏筱籌篔籤篠簡籙簀篋籜籮簞簫簣簍籃籛籬籪籟糴類秈糶糲粵糞糧糉糝餱糊餈系緊累縶縕緪糹糾紆紅紂纖"
    u"紇約級紈纊紀紉緯紜紘純紕紗綱納紝縱綸紛紙紋紡紵紖紐紓線紺紲紱練組紳細織終縐絆紼絀紹繹經紿綁絨結絝繞絰絎繪給絢絳絡絕絞統綆綃絹繡綌綏絛繼綈績緒綾緓續綺緋綽鞝緄繩維綿綬繃綢綯綹綣綜綻綰綠綴緇緙緗緘緬纜緹緲緝縕繢緦綞緞緶線緱縋緩締縷編緡緣縉縛縟縝縫縗縞纏縭縊縑繽縹縵縲纓縮繆繅纈繚繕繒繮繾繰繯繳纘罌網羅罰罷羆羈羥羨羣翹翽翬耇耮耬聳恥聶聾職聹聯聵聰肅腸膚骯餚腎腫脹脅胄膽背勝胡朧腖臚脛膠脈膾髒臍腦膿臠腳脫腡臉臘醃膕齶膩靦膃騰臏羶臢致輿舍艤艦艙艫艱豔"
    u"藝節羋薌蕪蘆芸蓯葦藶莧萇蒼苧蘇苔薴蘋範莖蘢蔦塋煢繭荊薦薘莢蕘蓽萴蕎薈薺蕩榮葷滎犖熒蕁藎蓀蔭蕒葒葤藥蒞萊蓮蒔萵薟獲蕕瑩鶯蓴蘀蘿螢營縈蕭薩蔥蒕蕆蕢蔣蔞醟蒙藍薊蘺蕷鎣驀虆蔑薔蘞藺藹薀蘄蘊藪蘚藤蘊櫱虜慮虛蟲虯蟣蝨雖蝦蠆蝕蟻螞蠁蠶蠔蜆蠱蠣蟶蠻蟄蛺蟯螄蠐蛻蝸蠟蠅蟈蟬蠍螻蠑螿蟎蠨釁銜補表襯袞襖嫋褘襪襲襏裝襠褌褳襝褲襉褸襤襴見觀覎規覓視覘覽覺覬覡覿覥覦覯覲覷觴觸觶誾讋譽謄訁計訂訃認譏訐訌討讓訕訖託訓議訊記訒講諱謳詎訝訥許訛論訩訟諷設訪訣證詁訶評詛識詗詐"
    u"訴診詆謅詞詘詔詖譯詒誆誄試詿詩詰詼誠誅詵話誕詬詮詭詢詣諍該詳詫諢詡譸誡誣語誚誤誥誘誨誑說誦誒請諸諏諾讀諑誹課諉諛誰諗調諂諒諄誶談讅誼謀諶諜謊諫諧謔謁謂諤諭諼讒諮諳諺諦謎諞諝謨讜謖謝謠謗諡謙謐謹謾謫譾謬譚譖譙讕譜譎讞譴譫讖谷豆象豶貝貞負貟貢財責賢敗賬貨質販貪貧貶購貯貫貳賤賁貰貼貴貺貸貿費賀貽賊贄賈賄貲賃賂贓資賅贐賕賑賚賒賦賭齎贖賞賜贔賙賡賠賧賴賵贅賻賺賽賾贗贊贇贈贍贏贛赬趙趕趨趲躉躍蹌蹠躒踐躂蹺蹕躚躋躊蹤躓躑躡蹣躕躥躪躦軀轀車軋軌軒軑軔轉"
    u"軛輪軟轟軲軻轤軸軹軼軤軫轢軺輕軾載輊轎輈輇輅較輒輔輛輦輩輝輥輞輬輟輜輳輻輯轀輸轡轅轄輾轆轍轔辭闢辯辮邊遼達遷過邁運還這進遠違連遲邇逕跡適選遜遞邐邏遺遙鄧鄺鄔郵鄒鄴鄰鬱郟鄶鄭鄆酈鄖鄲酇醞醱醬酸釅釃釀醞採釋裏鑑鑾鏨釒釓釔針釘釗釙釕釷釺釧釤鈒釩釣鍆釹鍚釵鈃鈣鈈鈦鉅鈍鈔鍾鈉鋇鋼鈑鈐鑰欽鈞鎢鉤鈧鈁鈥鈄鈕鈀鈺錢鉦鉗鈷鉢鈳鉕鈽鈸鉞鑽鉬鉭鉀鈿鈾鐵鉑鈴鑠鉛鉚鉋鈰鉉鉈鉍鈮鈹鐸鉶銬銠鉺鋩錏銪鋮鋏鋣鐃銍鐺銅鋁銱銦鎧鍘銖銑鋌銩銛鏵銓鎩鉿銚鉻銘錚銫鉸銥鏟銃鐋銨銀銣"
    u"鑄鐒鋪鋙錸鋱鏈鏗銷鎖鋰鋥鋤鍋鋯鋨鏽銼鋝鋒鋅鋶鐦鐧銳銻鋃鋟鋦錒錆鍺鍩錯錨錛錡鍀錁錕錩錫錮鑼錘錐錦鑕鍁錈鍃錇錟錠鍵鋸錳錙鍥鍈鍇鏘鍶鍔鍤鍬鍾鍛鎪鍠鍰鎄鍍鎂鏤鎡鐨鎇鏌鎮鎛鎘鑷钂鐫鎳鎿鎦鎬鎊鎰鎵鑌鎔鏢鏜鏝鏍鏰鏞鏡鏑鏃鏇鏐鐔钁鐐鏷鑥鐓鑭鐠鑹鏹鐙鑊鐳鐶鐲鐮鐿鑔鑣鑞鑱鑲長門閂閃閆閈閉問闖閏闈閒閎間閔閌悶閘鬧閨聞闥閩閭闓閥閣閡閫鬮閱閬闍閾閹閶鬩閿閽閻閼闡闌闃闠闊闋闔闐闒闕闞闤隊陽陰陣階際陸隴陳陘陝隯隉隕險隨隱隸雋難僱雛雕讎靂霧霽黴霢靄靚靝靜面靨韃鞽韉韝韋"
    u"韌韍韓韙韞韜韻頁頂頃頇項順須頊頑顧頓頎頒頌頏預顱領頗頸頡頰頲頜潁熲頦頤頻頮頹頷頴穎顆題顒顎顓顏額顳顢顛顙顥纇顫顬顰顴風颺颭颮颯颶颸颼颻飀飄飆飈飛饗饜飠飣飢飥餳飩餼飪飫飭飯飲餞飾飽飼飿飴餌饒餉餄餎餃餏餅餑餖餓餘餒餕餜餛餡館餷饋餶餿饞饁饃餺餾饈饉饅饊饌饢馬馭馱馴馳驅馹駁驢駔駛駟駙駒騶駐駝駑駕驛駘驍罵駰驕驊駱駭駢驫驪騁驗騂駸駿騏騎騍騅騌驌驂騙騭騤騷騖驁騮騫騸驃騾驄驏驟驥驦驤髏髖髕鬢鬹魘魎魚魛魢魷魨魯魴䰾魺鮁鮃鮎鱸鮋鮓鮒鮊鮑鱟鮍鮐鮭鮚鮳鮪鮞鮦鰂"
    u"鮜鱠鱭鮫鮮鮺鯗鱘鯁鱺鰱鰹鯉鰣鰷鯀鯊鯇鮶鯽鯒鯖鯪鯕鯫鯡鯤鯧鯝鯢鯰鯛鯨鰺鯴鯔鱝鰈鰏鱨鯷鰮鰃鰓鱷鰍鰒鰉鰁鱂鯿鰠鰲鰭鰨鰥鰩鰟鰜鰳鰾鱈鱉鰻鰵鱅䲁鰼鱖鱔鱗鱒鱯鱤鱧鱣䲘鳥鳩雞鳶鳴鳲鷗鴉鶬鴇鴆鴣鶇鸕鴨鴞鴦鴒鴟鴝鴛鷽鴕鷥鷙鴯鴰鵂鴴鵃鴿鸞鴻鵐鵓鸝鵑鵠鵝鵒鷳鵜鵡鵲鶓鵪鵾鵯鵬鵮鶉鶊鵷鷫鶘鶡鶚鶻鶖鷀鶥鶩鷊鷂鶲鶹鶺鷁鶼鶴鷖鸚鷓鷚鷯鷦鷲鷸鷺䴉鸇鷹鸌鸏鸛鸘鹺麥麩麴麪麼黃黌黶黷黲黽黿鼂鼉鼴齊齏齒齔齕齗齟齡齙齠齜齦齬齪齲齷龍龔龕龜䃮䥑鿓鎶"
)
_T2S_KEYS = (
    u"㑮㑯㑳㑶㒓㓄㓨㔋㖮㗿㘉㘓㘔㘚㛝㜄㜏㜐㜗㜷㞞㟺㠏㢗㢝㥮㦎㦛㦞㨻㩋㩜㩳㩵㪎㯤㰙㵗㵾㶆㷍㷿㸇㹽㺜㻶㿖㿗㿧䀉䀹䁻䂎䃮䅐䅳䆉䉑䉙䉬䉲䉶䊭䊷䊺䋃䋔䋙䋚䋦䋹䋻䋼䋿䌈䌋䌖䌝䌟䌥䌰䍤䍦䍽䎙䎱䕤䕳䖅䗅䗿䙔䙡䙱䚩䛄䛳䜀䜖䝭䝻䝼䞈䞋䞓䟃䟆䟐䠆䠱䡐䡩䢨䤤䥄䥇䥑䥗䥩䥯䥱䦘䦛䦟䦯䦳䪊䪏䪗䪘䪴䪾䫀䫂䫟䫴䫶䫻䫾䬓䬘䬝䬞䬧䭀䭃䭑䭔䭿䮝䮞䮠䮫䮰䮳䮾䯀䯤䰾䱀䱁䱙䱧䱬䱰䱷䱸䱽䲁䲅䲖䲘䲰䳜䳢䳤䳧䳫䴉䴋䴬䴱䴴䴽䵳䵴䶕䶲丟並么乾亂亙亞仝佇佈佔併來侖侶侷俁係俓俔俠俥俬俱倀倆倈倉個們倖倫"
    u"倲偉偑側偵偽傌傑傖傘備傢傭傯傳傴債傷傾僂僅僉像僑僕僞僥僨僱價儀儁儂億儈儉儎儐儔儕儘償儣優儭儲儷儸儺儻儼兇兌兒兗內兩冊冑冪凈凍凙凜凱別刪剄則剋剎剗剛剝剮剴創剷剾劃劄劇劉劊劌劍劏劑劚勁勑動務勛勝勞勢勣勩勱勳勵勸勻匭匯匱區協卹卻卽厙厠厤厭厲厴參叄叚叢吒吳吶呂咼員哩哯唄唓唸問啓啞啟啢喆喎喚喪喫喬單喲嗆嗇嗊嗎嗚嗩嗶嗹嘆嘍嘓嘔嘖嘗嘜嘩嘪嘮嘯嘰嘳嘵嘸嘺嘽噁噅噓噚噝噞噠噥噦噯噲噴噸噹嚀嚇嚌嚐嚕嚙嚛嚥嚦嚨嚮嚲嚳嚴嚶嚽囀囁囂囃囅囈囉囌囑囒囪圇國圍園圓圖團圞"
    u"坏垻埡埬埰執堃堅堊堖堚堝堯報場塊塋塏塒塗塚塢塤塵塹墊墜墮墰墲墳墶墻墾壇壈壋壎壓壘壙壚壜壞壟壠壢壣壩壪壯壺壼壽夠夢夥夾奐奧奩奪奬奮奼妝姍姦娛婁婡婦婭媈媧媯媰媼媽嫋嫗嫵嫺嫻嫿嬀嬃嬇嬈嬋嬌嬙嬡嬣嬤嬦嬪嬰嬸嬻孃孄孆孇孋孌孎孫學孾孿宮寀寠寢實寧審寫寬寵寶將專尋對導尷屆屍屓屜屢層屨屩屬岡峯峴島峽崍崑崗崙崢崬嵐嵗嵼嵾嶁嶄嶇嶈嶔嶗嶘嶠嶢嶧嶨嶮嶸嶹嶺嶼嶽巊巋巒巔巖巗巰巹帥師帳帶幀幃幓幗幘幝幟幣幩幫幬幷幹幾庫廁廂廄廈廎廕廚廝廟廠廡廢廣廧廩廬廳弒弔弳張強彃彆"
    u"彈彌彎彔彙彠彥彫彲彷彿後徑從徠復徵徹徿恆恥悅悞悵悶悽惡惱惲惻愛愜愨愴愷愻愾慄態慍慘慚慟慣慤慪慫慮慳慶慺慼慾憂憊憐憑憒憖憚憢憤憫憮憲憶憸憹懀懇應懌懍懎懞懟懣懤懨懲懶懷懸懺懼懾戀戇戔戧戩戰戱戲戶扞拋拚挩挱挾捨捫捱捲掃掄掆掗掙掚掛採揀揚換揮揯損搖搗搧搵搶摋摐摑摜摟摯摳摶摺摻撈撊撏撐撓撝撟撣撥撧撫撲撳撻撾撿擁擄擇擊擋擓擔據擟擠擡擣擫擬擯擰擱擲擴擷擺擻擼擽擾攄攆攋攏攔攖攙攛攜攝攢攣攤攪攬敎敓敗敘敵數斂斃斅斆斕斬斷斸於旂旣昇時晉晝暈暉暘暢暫曄曆曇曉"
    u"曊曏曖曠曨曬書會朧朮東枴柵柺査桿梔梖梘條梟梲棄棊棖棗棟棡棧棲棶椀椏椲楇楊楓楨業極榘榦榪榮榲榿構槍槓槤槧槨槫槮槳槶槼樁樂樅樑樓標樞樠樢樣樤樧樫樳樸樹樺樿橈橋機橢橫檁檉檔檜檟檢檣檭檮檯檳檵檸檻櫃櫅櫓櫚櫛櫝櫞櫟櫠櫥櫧櫨櫪櫫櫬櫱櫳櫸櫻欄欅欇權欍欏欐欑欒欖欘欞欽歎歐歟歡歲歷歸歿殘殞殢殤殨殫殭殮殯殰殲殺殻殼毀毆毊毿氂氈氌氣氫氬氭氳氾汎汙決沈沒沖況泝洩洶浹涇涗涼淒淚淥淨淩淪淵淶淺淼渙減渢渦測渾湊湞湧湯溈準溝溡溫溮溳溼滄滅滌滎滙滬滯滲滷滸滻滾滿漁漊漚漢"
    u"漣漬漲漵漸漿潁潑潔潙潚潛潣潤潯潰潷潿澀澂澅澆澇澐澗澠澤澦澩澬澮澱澾濁濃濄濕濘濚濛濜濟濤濧濫濰濱濺濼濾濿瀂瀃瀅瀆瀇瀉瀋瀏瀕瀘瀝瀟瀠瀦瀧瀨瀰瀲瀾灃灄灍灑灕灘灝灡灣灤灧灩災為烏烴無煇煉煒煙煢煥煩煬煱熂熅熉熌熒熓熗熚熡熱熲熾燁燈燉燒燙燜營燦燬燭燴燶燻燼燾爃爄爇爍爐爖爛爥爧爭爲爺爾牀牆牘牴牽犇犖犛犞犢犧狀狹狽猌猙猶猻獁獃獄獅獊獎獨獩獪獫獮獰獱獲獵獷獸獺獻獼玀玁珼現琱琺琿瑋瑒瑣瑤瑩瑪瑲瑻瑽璉璝璡璣璦璫璯環璵璸璼璽璾璿瓄瓊瓏瓔瓕瓚甌甕產産甦甯畝畢畫異"
    u"畵當畼疇疊痙痠痮痾瘂瘋瘍瘓瘞瘡瘧瘮瘱瘲瘺瘻療癆癇癉癐癒癘癟癡癢癤癥癧癩癬癭癮癰癱癲發皁皚皟皰皸皺盃盜盞盡監盤盧盨盪眝眞眥眾睏睜睞瞘瞜瞞瞤瞭瞶瞼矇矉矑矓矚矯硃硜硤硨硯碕碙碩碭碸確碼碽磑磚磠磣磧磯磽磾礄礆礎礒礙礦礪礫礬礮礱祇祕祿禍禎禕禡禦禪禮禰禱禿秈稅稈稏稜稟種稱穀穇穌積穎穠穡穢穩穫穭窩窪窮窯窵窶窺竄竅竇竈竊竚竪竱競筆筍筦筧筴箇箋箏箚節範築篋篔篘篠篤篩篳簀簂簍簑簞簡簢簣簫簹簽簾籃籋籌籔籙籛籜籟籠籤籩籪籬籮籲粵糉糝糞糧糰糲糴糶糹糺糾紀紂約紅紆"
    u"紇紈紉紋納紐紓純紕紖紗紘紙級紛紜紝紟紡紬紮細紱紲紳紵紹紺紼紿絀絁終絃組絅絆絍絎結絕絙絛絜絝絞絡絢絥給絧絨絰統絲絳絶絹綀綁綃綆綇綈綉綋綌綏綐綑經綜綞綟綠綢綣綫綬維綯綰綱網綳綴綵綸綹綺綻綽綾綿緄緇緊緋緍緑緒緓緔緗緘緙線緝緞緟締緡緣緤緦編緩緬緮緯緰緱緲練緶緷緸緹緻緼縈縉縊縋縍縎縐縑縕縗縛縝縞縟縣縧縫縬縭縮縰縱縲縳縴縵縶縷縸縹縺總績繂繃繅繆繈繏繐繒繓織繕繚繞繟繡繢繨繩繪繫繬繭繮繯繰繳繷繸繹繼繽繾繿纇纈纊續纍纏纓纔纖纗纘纚纜缽罃罈罌罎罰罵罷羅羆羈"
    u"羋羣羥羨義羵羶習翫翬翹翽耑耬耮聖聞聯聰聲聳聵聶職聹聻聽聾肅脅脈脛脣脥脩脫脹腎腖腡腦腪腫腳腸膃膕膚膞膠膩膹膽膾膿臉臍臏臗臘臚臟臠臢臥臨臺與興舉舊舖舘艙艣艤艦艫艱艷芻苧茲荊莊莖莢莧菉菕華菴菸萇萊萬萴萵葉葒葝葤葦葯葷蒐蒓蒔蒕蒞蒭蒼蓀蓆蓋蓧蓮蓯蓴蓽蔔蔘蔞蔣蔥蔦蔭蕁蕆蕎蕒蕓蕕蕘蕝蕢蕩蕪蕭蕳蕷蕽薀薆薈薊薌薑薔薘薟薦薩薳薴薵薹薺藉藍藎藝藥藪藭藴藶藷藹藺蘀蘄蘆蘇蘊蘋蘚蘞蘢蘭蘺蘿虆處虛虜號虧虯蛺蛻蜆蝕蝟蝦蝨蝸螄螞螢螮螻螿蟂蟄蟈蟎蟘蟜蟣蟬蟯蟲蟶蟻蠀蠁蠅蠆蠍"
    u"蠐蠑蠔蠙蠟蠣蠦蠨蠱蠶蠻蠾衆衊術衕衚衛衝衹袞袷裊裏補裝裡製複褌褘褲褳褸褻襇襉襏襓襖襗襘襝襠襤襪襬襯襰襲襴襵覆覈見覎規覓視覘覛覡覥覦親覬覯覲覷覹覺覼覽覿觀觴觶觸訁訂訃計訊訌討訐訑訒訓訕訖託記訛訜訝訞訟訢訣訥訨訩訪設許訴訶診註証詁詆詊詎詐詑詒詓詔評詖詗詘詛詞詠詡詢詣試詩詫詬詭詮詰話該詳詵詼詿誂誄誅誆誇誋誌認誑誒誕誘誚語誠誡誣誤誥誦誨說誫説誰課誳誴誶誷誹誺誼誾調諂諄談諉請諍諏諑諒論諗諛諜諝諞諡諢諣諤諥諦諧諫諭諮諯諰諱諳諶諷諸諺諼諾謀謁謂謄謅謆謉"
    u"謊謎謐謔謖謗謙謚講謝謠謡謨謫謬謭謯謱謳謸謹謾譁譂譅譆證譊譎譏譑譖識譙譚譜譟譨譫譭譯議譴護譸譽譾讀讅變讋讌讎讒讓讕讖讚讜讞谿豈豎豐豔豬豵豶貍貓貗貙貝貞貟負財貢貧貨販貪貫責貯貰貲貳貴貶買貸貺費貼貽貿賀賁賂賃賄賅資賈賊賑賒賓賕賙賚賜賝賞賟賠賡賢賣賤賦賧質賫賬賭賰賴賵賺賻購賽賾贃贄贅贇贈贉贊贋贍贏贐贑贓贔贖贗贚贛贜赬趕趙趨趲跡踐踰踴蹌蹔蹕蹟蹠蹣蹤蹳蹺蹻躂躉躊躋躍躎躑躒躓躕躘躚躝躡躥躦躪軀軉車軋軌軍軑軒軔軕軗軛軜軟軤軨軫軬軲軷軸軹軺軻軼軾軿較輅輇"
    u"輈載輊輒輓輔輕輖輛輜輝輞輟輢輥輦輨輩輪輬輯輳輷輸輻輼輾輿轀轂轄轅轆轇轉轊轍轎轐轔轗轟轠轡轢轣轤辦辭辮辯農迴迺逕這連週進遊運過達違遙遜遞遠遡適遱遲遶遷選遺遼邁還邇邊邏邐邨郟郵鄆鄉鄒鄔鄖鄟鄧鄭鄰鄲鄴鄶鄺酇酈醃醖醜醞醟醣醫醬醱醶釀釁釃釅釋釐釒釓釔釕釗釘釙釚針釟釣釤釦釧釨釩釲釳釵釷釹釺釾鈀鈁鈃鈄鈅鈆鈈鈉鈋鈍鈎鈐鈑鈒鈔鈕鈖鈗鈛鈞鈠鈡鈣鈥鈦鈧鈮鈯鈰鈲鈳鈴鈷鈸鈹鈺鈽鈾鈿鉀鉁鉅鉆鉈鉉鉋鉍鉑鉔鉕鉗鉚鉛鉞鉠鉢鉤鉦鉬鉭鉳鉶鉸鉺鉻鉽鉾鉿銀銁銂銃銅銊銍銏銑銓銖銘"
    u"銚銛銜銠銣銥銦銨銩銪銫銬銱銳銷銹銻銼鋁鋂鋃鋅鋇鋉鋌鋏鋒鋙鋝鋟鋠鋣鋤鋥鋦鋨鋩鋪鋭鋮鋯鋰鋱鋶鋸鋼錁錂錄錆錇錈錏錐錒錕錘錙錚錛錜錝錟錠錡錢錥錦錨錩錫錮錯録錳錶錸錼錽鍀鍁鍃鍄鍅鍆鍇鍈鍉鍊鍋鍍鍒鍔鍘鍚鍛鍠鍤鍥鍩鍬鍮鍰鍵鍶鍺鍼鍾鎂鎄鎇鎈鎊鎌鎍鎔鎖鎘鎙鎚鎛鎞鎡鎢鎣鎦鎧鎩鎪鎬鎭鎮鎯鎰鎲鎳鎵鎶鎷鎸鎿鏃鏆鏇鏈鏉鏌鏍鏐鏑鏗鏘鏚鏜鏝鏞鏟鏡鏢鏤鏥鏦鏨鏰鏵鏷鏹鏺鏽鏾鐃鐈鐋鐎鐐鐒鐓鐔鐘鐙鐝鐠鐥鐦鐧鐨鐪鐫鐮鐯鐲鐳鐵鐶鐸鐺鐼鐿鑀鑄鑉鑊鑌鑑鑒鑔鑕鑞鑠鑣鑥鑪鑭鑰鑱鑲鑴鑷鑹鑼"
    u"鑽鑾鑿钁钂長門閂閃閆閈閉開閌閍閎閏閐閑閒間閔閗閘閝閞閡閣閤閥閨閩閫閬閭閱閲閵閶閹閻閼閽閾閿闃闆闇闈闊闋闌闍闐闒闓闔闕闖關闞闠闡闢闤闥阪陘陝陞陣陰陳陸陽隉隊階隕際隨險隯隱隴隸隻雋雖雙雛雜雞離難雲電霑霢霣霧霼霽靂靄靆靈靉靚靜靝靦靧靨鞏鞝鞦鞽鞾韁韃韆韉韋韌韍韓韙韚韛韜韝韞韠韻響頁頂頃項順頇須頊頌頎頏預頑頒頓頗領頜頡頤頦頫頭頮頰頲頴頷頸頹頻頽顂顃顅顆題額顎顏顒顓顔願顙顛類顢顣顥顧顫顬顯顰顱顳顴風颭颮颯颰颱颳颶颷颸颺颻颼颾飀飄飆飈飋飛飠飢飣飥飦飩"
    u"飪飫飭飯飱飲飴飵飶飼飽飾飿餃餄餅餈餉養餌餎餏餑餒餓餔餕餖餘餚餛餜餞餡餦餧館餪餫餬餭餱餳餵餶餷餺餼餾餿饁饃饅饈饉饊饋饌饑饒饗饜饞饟饠饢馬馭馮馯馱馳馴馹駁駊駎駐駑駒駔駕駘駙駚駛駝駞駟駡駢駤駧駩駫駭駰駱駶駸駻駿騁騂騃騅騉騌騍騎騏騔騖騙騚騜騝騟騤騧騪騫騭騮騰騴騶騷騸騻騼騾驀驁驂驃驄驅驊驋驌驍驏驓驕驗驙驚驛驟驢驤驥驦驨驪驫骯髏髒體髕髖髮鬆鬍鬖鬚鬠鬢鬥鬧鬨鬩鬮鬱鬹魎魘魚魛魢魥魦魨魯魴魵魷魺魽鮁鮃鮄鮅鮊鮋鮍鮎鮐鮑鮒鮓鮚鮜鮝鮞鮣鮤鮦鮪鮫鮭鮮鮯鮰鮳鮵鮶鮺"
    u"鮿鯀鯁鯄鯆鯇鯉鯊鯒鯔鯕鯖鯗鯛鯝鯞鯡鯢鯤鯧鯨鯪鯫鯬鯰鯱鯴鯶鯷鯽鯾鯿鰁鰂鰃鰆鰈鰉鰋鰌鰍鰏鰐鰑鰒鰓鰕鰛鰜鰟鰠鰣鰥鰦鰧鰨鰩鰫鰭鰮鰱鰲鰳鰵鰷鰹鰺鰻鰼鰽鰾鱂鱄鱅鱆鱈鱉鱊鱒鱔鱖鱗鱘鱝鱟鱠鱢鱣鱤鱧鱨鱭鱮鱯鱷鱸鱺鳥鳧鳩鳬鳲鳳鳴鳶鳷鳼鳽鳾鴀鴃鴅鴆鴇鴉鴐鴒鴔鴕鴗鴛鴜鴝鴞鴟鴣鴥鴦鴨鴮鴯鴰鴲鴳鴴鴷鴻鴽鴿鵁鵂鵃鵊鵐鵑鵒鵓鵚鵜鵝鵠鵡鵧鵩鵪鵫鵬鵮鵯鵰鵲鵷鵾鶄鶇鶉鶊鶌鶒鶓鶖鶗鶘鶚鶡鶥鶦鶩鶪鶬鶭鶯鶰鶲鶴鶹鶺鶻鶼鶿鷀鷁鷂鷄鷅鷉鷊鷐鷓鷔鷖鷗鷙鷚鷣鷤鷥鷦鷨鷩鷫鷯鷲鷳鷴鷷鷸鷹鷺鷽"
    u"鷿鸂鸇鸊鸋鸌鸏鸕鸗鸘鸚鸛鸝鸞鹵鹹鹺鹼鹽麗麥麨麩麪麫麯麲麴麵麷麼麽黃黌點黨黲黴黶黷黽黿鼂鼉鼕鼴齊齋齎齏齒齔齕齗齙齜齟齠齡齣齦齧齩齪齬齭齰齲齴齶齷齾龍龎龐龑龓龔龕龜龢龭龯鿁鿓"
)
_T2S_VALS = (
    u"㑮㑔㑇㐹㒓㓄刾㔋㖮㗿㘉㘓㘔㘎㛝㚯㛣㜐㜗㜷㞞㟺㟆㢗㢝㤘㦎㦛㦞㨻㩋㨫㧐擜㪎㯤㰙㵗㵾㶆㷍㷿㸇㹽㺜㻶㿖㿗㿧䀉䀹䀥䂎鿎䅐䅳䆉䉑䉙䉬䉲䉶䊭䌶䊺䋃䋔䌺䌻䋦䌿䌾䋼䋿䌈䌋䌖䌝䌟䌥䌰䍤䍠䍽䎙䎬䕤䕳䖅䗅䗿䙔䙌䙱䚩䛄䛳䜧䜖䝭䝻䞍䞈䞋䞓䟃䟆䟐䠆䠱䡐䡩䢨䤤䥄䦂鿏䥗䥩䥯䥾䦘䦶䦷䦯䦳䪊䪏䪗䪘䪴䪾䫀䫂䫟䫴䫶䫻䫾䬓䬘䬝䬞䬧䭀䭃䭑䭔䭿䮝䮞䮠䮫䮰䮳䮾䯅䯤鲃䱀䱁䱙䱧䱬䱰䲣䱸䲝鳚䲅䲖鳤䲰䳜䳢䳤䳧䳫鹮䴋䴬䴱䴴䴽䵳䵴䶕䶲丢并么干乱亘亚仝伫布占并来仑侣局俣系俓伣侠伡私俱伥俩俫仓个们幸伦"
    u"㑈伟㐽侧侦伪㐷杰伧伞备家佣偬传伛债伤倾偻仅佥像侨仆伪侥偾雇价仪俊侬亿侩俭傤傧俦侪尽偿儣优儭储俪㑩傩傥俨凶兑儿兖内两册胄幂净冻凙凛凯别删刭则克刹刬刚剥剐剀创铲剾划札剧刘刽刿剑㓥剂㔉劲勑动务勋胜劳势绩勚劢勋励劝匀匦汇匮区协恤却即厍厕历厌厉厣参叁叚丛咤吴呐吕呙员哩哯呗唓念问启哑启唡喆㖞唤丧吃乔单哟呛啬唝吗呜唢哔嗹叹喽啯呕啧尝唛哗嘪唠啸叽嘳哓呒嘺啴恶噅嘘㖊咝噞哒哝哕嗳哙喷吨当咛吓哜尝噜啮嚛咽呖咙向亸喾严嘤嚽啭嗫嚣囃冁呓啰苏嘱囒囱囵国围园圆图团圞"
    u"坏坝垭埬采执堃坚垩垴堚埚尧报场块茔垲埘涂冢坞埙尘堑垫坠堕坛墲坟垯墙垦坛壈垱埙压垒圹垆坛坏垄垅坜壣坝塆壮壶壸寿够梦伙夹奂奥奁夺奖奋姹妆姗奸娱娄婡妇娅媈娲妫㛀媪妈袅妪妩娴娴婳妫媭嬇娆婵娇嫱嫒嬣嬷嬦嫔婴婶嬻娘孄孆孇㛤娈孎孙学孾孪宫采寠寝实宁审写宽宠宝将专寻对导尴届尸屃屉屡层屦屩属冈峰岘岛峡崃昆岗仑峥岽岚岁嵼㟥嵝崭岖嶈嵚崂嶘峤峣峄峃崄嵘嶹岭屿岳巊岿峦巅岩巗巯卺帅师帐带帧帏㡎帼帻幝帜币幩帮帱并干几库厕厢厩厦庼荫厨厮庙厂庑废广廧廪庐厅弑吊弪张强彃别"
    u"弹弥弯录汇彟彦雕彨彷佛后径从徕复征彻徿恒耻悦悮怅闷凄恶恼恽恻爱惬悫怆恺愻忾栗态愠惨惭恸惯悫怄怂虑悭庆㥪戚欲忧惫怜凭愦慭惮憢愤悯怃宪忆憸憹懀恳应怿懔懎蒙怼懑㤽恹惩懒怀悬忏惧慑恋戆戋戗戬战戯戏户捍抛拼捝挲挟舍扪挨卷扫抡㧏挜挣掚挂采拣扬换挥搄损摇捣扇揾抢摋摐掴掼搂挚抠抟折掺捞撊挦撑挠㧑挢掸拨撧抚扑揿挞挝捡拥掳择击挡㧟担据擟挤抬捣擫拟摈拧搁掷扩撷摆擞撸㧰扰摅撵攋拢拦撄搀撺携摄攒挛摊搅揽教敚败叙敌数敛毙斅敩斓斩断斸于旗既升时晋昼晕晖旸畅暂晔历昙晓"
    u"曊向暧旷昽晒书会胧术东拐栅拐查杆栀梖枧条枭棁弃棋枨枣栋㭎栈栖梾椀桠㭏楇杨枫桢业极矩干杩荣榅桤构枪杠梿椠椁槫椮桨椢椝桩乐枞梁楼标枢樠㭤样樤榝㭴桪朴树桦椫桡桥机椭横檩柽档桧槚检樯檭梼台槟檵柠槛柜櫅橹榈栉椟橼栎櫠橱槠栌枥橥榇蘖栊榉樱栏榉欇权欍椤欐欑栾榄欘棂钦叹欧欤欢岁历归殁残殒殢殇㱮殚僵殓殡㱩歼杀壳壳毁殴毊毵牦毡氇气氢氩氭氲泛泛污决沈没冲况溯泄汹浃泾涚凉凄泪渌净凌沦渊涞浅淼涣减沨涡测浑凑浈涌汤沩准沟溡温浉涢湿沧灭涤荥汇沪滞渗卤浒浐滚满渔溇沤汉"
    u"涟渍涨溆渐浆颍泼洁沩㴋潜潣润浔溃滗涠涩澂澅浇涝沄涧渑泽滪泶澬浍淀㳠浊浓㳡湿泞溁蒙浕济涛㳔滥潍滨溅泺滤濿澛瀃滢渎㲿泻沈浏濒泸沥潇潆潴泷濑弥潋澜沣滠灍洒漓滩灏㳕湾滦滟滟灾为乌烃无煇炼炜烟茕焕烦炀㶽熂煴熉熌荧熓炝熚熡热颎炽烨灯炖烧烫焖营灿毁烛烩㶶熏烬焘爃爄爇烁炉爖烂爥爧争为爷尔床墙牍抵牵犇荦牦犞犊牺状狭狈猌狰犹狲犸呆狱狮獊奖独獩狯猃狝狞㺍获猎犷兽獭献猕猡玁珼现雕珐珲玮玚琐瑶莹玛玱瑻瑽琏璝琎玑瑷珰㻅环玙瑸璼玺璾璇瓄琼珑璎瓕瓒瓯瓮产产甦甯亩毕画异"
    u"画当畼畴叠痉酸痮疴痖疯疡痪瘗疮疟瘆瘱疭瘘瘘疗痨痫瘅癐愈疠瘪痴痒疖症疬癞癣瘿瘾痈瘫癫发皂皑皟疱皲皱杯盗盏尽监盘卢盨荡眝真眦众困睁睐眍䁖瞒瞤瞭瞆睑蒙矉矑眬瞩矫朱硁硖砗砚埼碙硕砀砜确码䂵硙砖硵碜碛矶硗䃅硚礆础礒碍矿砺砾矾礮砻祇秘禄祸祯祎祃御禅礼祢祷秃籼税秆䅉棱禀种称谷䅟稣积颖秾穑秽稳获穞窝洼穷窑窎窭窥窜窍窦灶窃竚竖竱竞笔笋筦笕䇲个笺筝札节范筑箧筼篘筿笃筛筚箦簂篓蓑箪简簢篑箫筜签帘篮籋筹䉤箓篯箨籁笼签笾簖篱箩吁粤粽糁粪粮团粝籴粜纟糺纠纪纣约红纡"
    u"纥纨纫纹纳纽纾纯纰纼纱纮纸级纷纭纴紟纺䌷扎细绂绁绅纻绍绀绋绐绌絁终弦组䌹绊絍绗结绝絙绦絜绔绞络绚絥给絧绒绖统丝绛绝绢綀绑绡绠綇绨绣綋绤绥䌼捆经综缍綟绿绸绻线绶维绹绾纲网绷缀彩纶绺绮绽绰绫绵绲缁紧绯緍绿绪绬绱缃缄缂线缉缎緟缔缗缘緤缌编缓缅緮纬緰缑缈练缏緷緸缇致缊萦缙缢缒縍縎绉缣缊缞缚缜缟缛县绦缝縬缡缩縰纵缧䌸纤缦絷缕縸缥縺总绩繂绷缫缪繈繏繐缯繓织缮缭绕繟绣缋繨绳绘系繬茧缰缳缲缴繷䍁绎继缤缱䍀颣缬纩续累缠缨才纤纗缵纚缆钵䓨坛罂坛罚骂罢罗罴羁"
    u"芈群羟羡义羵膻习玩翚翘翙耑耧耢圣闻联聪声耸聩聂职聍聻听聋肃胁脉胫唇脥修脱胀肾胨脶脑腪肿脚肠腽腘肤䏝胶腻膹胆脍脓脸脐膑臗腊胪脏脔臜卧临台与兴举旧铺馆舱艣舣舰舻艰艳刍苎兹荆庄茎荚苋菉菕华庵烟苌莱万荝莴叶荭葝荮苇药荤搜莼莳蒀莅蒭苍荪席盖蓧莲苁莼荜卜参蒌蒋葱茑荫荨蒇荞荬芸莸荛蕝蒉荡芜萧蕳蓣蕽蕰薆荟蓟芗姜蔷荙莶荐萨薳苧䓓苔荠藉蓝荩艺药薮䓖蕴苈藷蔼蔺萚蕲芦苏蕴苹藓蔹茏兰蓠萝蔂处虚虏号亏虬蛱蜕蚬蚀猬虾虱蜗蛳蚂萤䗖蝼螀蟂蛰蝈螨蟘蟜虮蝉蛲虫蛏蚁蠀蚃蝇虿蝎"
    u"蛴蝾蚝蠙蜡蛎蠦蟏蛊蚕蛮蠾众蔑术同胡卫冲衹衮夹袅里补装里制复裈袆裤裢褛亵裥裥袯襓袄襗襘裣裆褴袜摆衬襰袭襕襵覆核见觃规觅视觇覛觋觍觎亲觊觏觐觑覹觉覼览觌观觞觯触讠订讣计讯讧讨讦訑讱训讪讫托记讹訜讶訞讼䜣诀讷訨讻访设许诉诃诊注证诂诋詊讵诈詑诒詓诏评诐诇诎诅词咏诩询诣试诗诧诟诡诠诘话该详诜诙诖誂诔诛诓夸誋志认诳诶诞诱诮语诚诫诬误诰诵诲说誫说谁课誳誴谇誷诽誺谊訚调谄谆谈诿请诤诹诼谅论谂谀谍谞谝谥诨諣谔諥谛谐谏谕咨諯諰讳谙谌讽诸谚谖诺谋谒谓誊诌謆謉"
    u"谎谜谧谑谡谤谦谥讲谢谣谣谟谪谬谫謯謱讴謸谨谩哗譂譅譆证譊谲讥譑谮识谯谭谱噪譨谵毁译议谴护诪誉谫读谉变詟䜩雠谗让谰谶赞谠谳溪岂竖丰艳猪豵豮狸猫貗䝙贝贞贠负财贡贫货贩贪贯责贮贳赀贰贵贬买贷贶费贴贻贸贺贲赂赁贿赅资贾贼赈赊宾赇赒赉赐賝赏賟赔赓贤卖贱赋赕质赍账赌䞐赖赗赚赙购赛赜贃贽赘赟赠贉赞赝赡赢赆贑赃赑赎赝贚赣赃赪赶赵趋趱迹践逾踊跄蹔跸迹跖蹒踪蹳跷蹻跶趸踌跻跃䟢踯跞踬蹰躘跹躝蹑蹿躜躏躯軉车轧轨军轪轩轫軕軗轭軜软轷軨轸軬轱軷轴轵轺轲轶轼軿较辂辁"
    u"辀载轾辄挽辅轻輖辆辎辉辋辍輢辊辇輨辈轮辌辑辏輷输辐辒辗舆辒毂辖辕辘轇转轊辙轿轐辚轗轰轠辔轹轣轳办辞辫辩农回迺径这连周进游运过达违遥逊递远溯适遱迟绕迁选遗辽迈还迩边逻逦邨郏邮郓乡邹邬郧鄟邓郑邻郸邺郐邝酂郦腌酝丑酝蒏糖医酱酦醶酿衅酾酽释厘钅钆钇钌钊钉钋釚针釟钓钐扣钏釨钒釲釳钗钍钕钎䥺钯钫钘钭钥鈆钚钠鈋钝钩钤钣钑钞钮鈖鈗鈛钧鈠钟钙钬钛钪铌鈯铈鈲钶铃钴钹铍钰钸铀钿钾鉁巨钻铊铉铇铋铂鉔钷钳铆铅钺鉠钵钩钲钼钽锫铏铰铒铬鉽鉾铪银銁銂铳铜銊铚銏铣铨铢铭"
    u"铫铦衔铑铷铱铟铵铥铕铯铐铞锐销锈锑锉铝鋂锒锌钡鋉铤铗锋铻锊锓鋠铘锄锃锔锇铓铺锐铖锆锂铽锍锯钢锞錂录锖锫锩铔锥锕锟锤锱铮锛錜錝锬锭锜钱錥锦锚锠锡锢错录锰表铼镎錽锝锨锪鍄钫钔锴锳鍉炼锅镀鍒锷铡钖锻锽锸锲锘锹鍮锾键锶锗针钟镁锿镅鎈镑镰鎍镕锁镉鎙锤镈鎞镃钨蓥镏铠铩锼镐镇镇鎯镒镋镍镓鿔鎷镌镎镞鏆旋链鏉镆镙镠镝铿锵鏚镗镘镛铲镜镖镂鏥鏦錾镚铧镤镪䥽锈鏾铙鐈铴鐎镣铹镦镡钟镫镢镨䦅锎锏镄鐪镌镰䦃镯镭铁镮铎铛鐼镱鑀铸鑉镬镔鉴鉴镲锧镴铄镳镥炉镧钥镵镶鑴镊镩锣"
    u"钻銮凿镢镋长门闩闪闫闬闭开闶閍闳闰閐闲闲间闵閗闸閝閞阂阁合阀闺闽阃阆闾阅阅閵阊阉阎阏阍阈阌阒板暗闱阔阕阑阇阗阘闿阖阙闯关阚阓阐辟阛闼阪陉陕升阵阴陈陆阳陧队阶陨际随险陦隐陇隶只隽虽双雏杂鸡离难云电沾霡霣雾霼霁雳霭叇灵叆靓静靔腼靧靥巩绱秋鞒鞾缰鞑千鞯韦韧韨韩韪韚韛韬鞲韫韠韵响页顶顷项顺顸须顼颂颀颃预顽颁顿颇领颌颉颐颏俯头颒颊颋颕颔颈颓频颓顂顃顅颗题额颚颜颙颛颜愿颡颠类颟顣颢顾颤颥显颦颅颞颧风飐飑飒颰台刮飓颷飔飏飖飕颾飗飘飙飚飋飞饣饥饤饦飦饨"
    u"饪饫饬饭飧饮饴飵飶饲饱饰饳饺饸饼糍饷养饵饹饻饽馁饿餔馂饾余肴馄馃饯馅餦餧馆餪餫糊餭糇饧喂馉馇馎饩馏馊馌馍馒馐馑馓馈馔饥饶飨餍馋饟饠馕马驭冯馯驮驰驯驲驳駊駎驻驽驹驵驾骀驸駚驶驼駞驷骂骈駤駧駩駫骇骃骆駶骎駻骏骋骍騃骓騉骔骒骑骐騔骛骗騚騜騝騟骙䯄騪骞骘骝腾騴驺骚骟騻騼骡蓦骜骖骠骢驱骅驋骕骁骣驓骄验驙惊驿骤驴骧骥骦驨骊骉肮髅脏体髌髋发松胡鬖须鬠鬓斗闹哄阋阄郁鬶魉魇鱼鱽鱾魥魦鲀鲁鲂魵鱿鲄魽鲅鲆鮄鮅鲌鲉鲏鲇鲐鲍鲋鲊鲒鲘鲞鲕䲟鮤鲖鲔鲛鲑鲜鮯鮰鲓鮵鲪鲝"
    u"鮿鲧鲠鯄鯆鲩鲤鲨鲬鲻鲯鲭鲞鲷鲴鯞鲱鲵鲲鲳鲸鲮鲰鯬鲶鯱鲺鯶鳀鲫鯾鳊鳈鲗鳂䲠鲽鳇鰋䲡鳅鲾鳄鰑鳆鳃鰕鳁鳒鳑鳋鲥鳏鰦䲢鳎鳐鰫鳍鳁鲢鳌鳓鳘鲦鲣鲹鳗鳛鰽鳔鳉鱄鳙鱆鳕鳖鱊鳟鳝鳜鳞鲟鲼鲎鲙鱢鳣鳡鳢鲿鲚鱮鳠鳄鲈鲡鸟凫鸠凫鸤凤鸣鸢鳷鳼鳽䴓鴀鴃鴅鸩鸨鸦鴐鸰鴔鸵鴗鸳鴜鸲鸮鸱鸪鴥鸯鸭鴮鸸鸹鴲鴳鸻䴕鸿鴽鸽䴔鸺鸼鵊鹀鹃鹆鹁鵚鹈鹅鹄鹉鵧鵩鹌鵫鹏鹐鹎雕鹊鹓鹍䴖鸫鹑鹒鶌鶒鹋鹙鶗鹕鹗鹖鹛鶦鹜䴗鸧鶭莺鶰鹟鹤鹠鹡鹘鹣鹚鹚鹢鹞鸡鷅䴘鹝鷐鹧鷔鹥鸥鸷鹨鷣鷤鸶鹪鷨鷩鹔鹩鹫鹇鹇鷷鹬鹰鹭鸴"
    u"鷿㶉鹯䴙鸋鹱鹲鸬鸗鹴鹦鹳鹂鸾卤咸鹾碱盐丽麦麨麸面面曲麲曲面麷么么黄黉点党黪霉黡黩黾鼋鼌鼍冬鼹齐斋赍齑齿龀龁龂龅龇龃龆龄出龈啮齩龊龉齭齰龋齴腭龌齾龙厐庞䶮龓龚龛龟龢龭龯䜤鿒"
)
_S2T_AMBIG = {
    u"㐹": u"㑶㐹",
    u"万": u"萬万",
    u"丑": u"醜丑",
    u"个": u"個箇",
    u"丰": u"豐丰",
    u"了": u"了瞭",
    u"于": u"於于",
    u"云": u"雲云",
    u"亘": u"亙亘",
    u"仆": u"僕仆",
    u"仇": u"仇讎",
    u"仑": u"侖崙",
    u"价": u"價价",
    u"仿": u"仿彷",
    u"伙": u"夥伙",
    u"余": u"餘余",
    u"佛": u"佛彿",
    u"佣": u"傭佣",
    u"俊": u"俊儁",
    u"修": u"修脩",
    u"借": u"借藉",
    u"僵": u"僵殭",
    u"克": u"克剋",
    u"党": u"黨党",
    u"具": u"具俱",
    u"冢": u"冢塚",
    u"冬": u"冬鼕",
    u"冲": u"衝沖",
    u"凄": u"悽淒",
    u"准": u"準准",
    u"凌": u"凌淩",
    u"几": u"幾几",
    u"凶": u"兇凶",
    u"出": u"出齣",
    u"划": u"劃划",
    u"别": u"別彆",
    u"刮": u"刮颳",
    u"制": u"制製",
    u"勋": u"勳勛",
    u"千": u"千韆",
    u"升": u"升昇",
    u"卜": u"卜蔔",
    u"占": u"佔占",
    u"卤": u"滷鹵",
    u"卷": u"卷捲",
    u"厂": u"廠厂",
    u"历": u"歷曆",
    u"厘": u"釐厘",
    u"参": u"參蔘",
    u"发": u"發髮",
    u"只": u"只隻祇",
    u"台": u"臺檯颱台",
    u"叶": u"葉叶",
    u"叹": u"嘆歎",
    u"吁": u"籲吁",
    u"吃": u"喫吃",
    u"合": u"合閤",
    u"吊": u"吊弔",
    u"同": u"同衕",
    u"后": u"後后",
    u"向": u"向嚮曏",
    u"吣": u"吣唚",
    u"呆": u"呆待",
    u"周": u"周週賙",
    u"咨": u"諮咨",
    u"咸": u"鹹咸",
    u"咽": u"咽嚥",
    u"哄": u"哄鬨",
    u"哗": u"譁嘩",
    u"唇": u"脣唇",
    u"啮": u"齧嚙",
    u"喂": u"喂餵",
    u"噪": u"噪譟",
    u"回": u"回迴",
    u"团": u"團糰",
    u"困": u"困睏",
    u"坐": u"坐座",
    u"坛": u"壇罈",
    u"坝": u"壩垻",
    u"坯": u"坯坏",
    u"埙": u"壎塤",
    u"堤": u"堤隄",
    u"复": u"復複覆",
    u"夫": u"夫伕",
    u"夸": u"誇夸",
    u"夹": u"夾袷",
    u"奸": u"奸姦",
    u"姜": u"姜薑",
    u"娘": u"娘孃",
    u"娴": u"嫺嫻",
    u"宁": u"寧甯",
    u"它": u"它牠",
    u"家": u"家傢",
    u"尝": u"嘗嚐",
    u"尸": u"屍尸",
    u"尽": u"盡儘",
    u"局": u"局侷",
    u"岩": u"巖岩",
    u"岳": u"嶽岳",
    u"巨": u"巨鉅",
    u"布": u"布佈",
    u"帘": u"簾帘",
    u"席": u"席蓆",
    u"干": u"幹乾干榦",
    u"并": u"並併幷",
    u"幸": u"幸倖",
    u"广": u"廣广",
    u"庵": u"庵菴",
    u"弥": u"彌瀰",
    u"弦": u"弦絃",
    u"当": u"當噹",
    u"录": u"錄彔",
    u"彩": u"彩綵",
    u"征": u"徵征",
    u"径": u"徑逕",
    u"御": u"御禦",
    u"志": u"志誌",
    u"念": u"念唸",
    u"恤": u"恤卹",
    u"恶": u"惡噁",
    u"愈": u"愈癒",
    u"愿": u"願愿",
    u"戚": u"戚慼鏚",
    u"扇": u"扇搧",
    u"才": u"才纔",
    u"扎": u"扎紮",
    u"托": u"托託",
    u"扣": u"扣釦",
    u"折": u"折摺",
    u"抵": u"抵牴",
    u"拐": u"拐柺",
    u"拿": u"拿拏",
    u"挂": u"掛挂",
    u"挨": u"挨捱",
    u"挽": u"挽輓",
    u"捆": u"捆綑",
    u"捍": u"捍扞",
    u"据": u"據据",
    u"搜": u"搜蒐",
    u"摆": u"擺襬",
    u"斗": u"鬥斗",
    u"斤": u"斤觔",
    u"斫": u"斫斲",
    u"旋": u"旋鏇",
    u"昆": u"昆崑",
    u"暗": u"暗闇",
    u"曲": u"曲麴",
    u"札": u"札劄",
    u"术": u"術朮",
    u"朱": u"朱硃",
    u"朴": u"樸朴",
    u"杆": u"杆桿",
    u"杠": u"槓杠",
    u"杯": u"杯盃",
    u"杰": u"傑杰",
    u"松": u"松鬆",
    u"板": u"板闆",
    u"极": u"極极",
    u"果": u"果菓",
    u"枪": u"槍鎗",
    u"柜": u"櫃柜",
    u"栗": u"栗慄",
    u"核": u"核覈",
    u"梁": u"梁樑",
    u"棱": u"棱稜",
    u"檗": u"檗蘗",
    u"欲": u"欲慾",
    u"毁": u"毀燬譭",
    u"汇": u"匯彙滙",
    u"沈": u"沈瀋",
    u"沾": u"沾霑",
    u"泛": u"泛氾汎",
    u"注": u"注註",
    u"浚": u"浚濬",
    u"涂": u"塗涂",
    u"涌": u"湧涌",
    u"淀": u"澱淀",
    u"游": u"遊游",
    u"溪": u"溪谿",
    u"滟": u"灩灧",
    u"漓": u"漓灕",
    u"澄": u"澄澂",
    u"炼": u"煉鍊",
    u"烟": u"煙菸",
    u"焰": u"焰燄",
    u"熏": u"燻熏薰",
    u"狸": u"狸貍",
    u"玩": u"玩翫",
    u"琅": u"琅瑯",
    u"璇": u"璇璿",
    u"症": u"症癥",
    u"皂": u"皁皂",
    u"矩": u"矩榘",
    u"确": u"確确",
    u"硷": u"硷礆鹼",
    u"私": u"私俬",
    u"秋": u"秋鞦",
    u"种": u"種种",
    u"穗": u"穗繐",
    u"筑": u"築筑",
    u"筱": u"筱篠",
    u"签": u"籤簽",
    u"糊": u"糊餬",
    u"系": u"系係繫",
    u"累": u"累纍",
    u"纤": u"纖縴",
    u"绱": u"鞝緔",
    u"绷": u"繃綳",
    u"耇": u"耇耈",
    u"胄": u"胄冑",
    u"背": u"背揹",
    u"胜": u"勝胜",
    u"胡": u"胡鬍衚",
    u"脏": u"髒臟",
    u"腊": u"臘腊",
    u"腌": u"醃腌",
    u"膻": u"羶膻",
    u"致": u"致緻",
    u"舍": u"舍捨",
    u"艳": u"豔艷",
    u"芸": u"芸蕓",
    u"苏": u"蘇甦囌",
    u"苔": u"苔薹",
    u"苹": u"蘋苹",
    u"范": u"範范",
    u"荐": u"薦荐",
    u"荡": u"蕩盪",
    u"荫": u"蔭廕",
    u"药": u"藥葯",
    u"获": u"獲穫",
    u"蒙": u"蒙矇濛懞",
    u"蔑": u"蔑衊",
    u"藤": u"藤籐",
    u"虫": u"蟲虫",
    u"蚝": u"蠔蚝",
    u"蜡": u"蠟蜡",
    u"蝎": u"蠍蝎",
    u"表": u"表錶",
    u"袅": u"嫋裊",
    u"裥": u"襉襇",
    u"证": u"證証",
    u"谥": u"諡謚",
    u"谷": u"谷穀",
    u"豆": u"豆荳",
    u"象": u"象像",
    u"赝": u"贗贋",
    u"赞": u"贊讚",
    u"跖": u"蹠跖",
    u"辟": u"闢辟",
    u"迹": u"跡蹟",
    u"适": u"適适",
    u"郁": u"鬱郁",
    u"酸": u"酸痠",
    u"采": u"採采寀",
    u"里": u"裏里哩",
    u"鉴": u"鑑鑒",
    u"针": u"針鍼",
    u"钟": u"鍾鐘鈡",
    u"钥": u"鑰鈅",
    u"钫": u"鈁鍅",
    u"钻": u"鑽鉆",
    u"铲": u"鏟剷",
    u"链": u"鏈鍊",
    u"锄": u"鋤耡",
    u"锫": u"錇鉳",
    u"镋": u"钂鎲",
    u"镎": u"鎿錼",
    u"镢": u"钁鐝",
    u"镰": u"鐮鎌",
    u"闲": u"閒閑",
    u"雇": u"僱雇",
    u"雕": u"雕鵰",
    u"面": u"面麪",
    u"须": u"須鬚",
    u"饥": u"飢饑",
    u"鹇": u"鷳鷴",
}
_S2T_MAP = dict(zip(_S2T_KEYS, _S2T_VALS))
_T2S_MAP = dict(zip(_T2S_KEYS, _T2S_VALS))

# ---------------------------------------------------------------- MD5

def _md5(data):
    if hashlib is not None:
        return hashlib.md5(data).digest()
    return _md5_pure(data)


def _md5_pure(data):
    """纯 Python MD5 (环境无 hashlib 时兜底)。"""
    import struct

    msg = bytearray(data)
    ml = len(msg) * 8
    msg.append(0x80)
    while len(msg) % 64 != 56:
        msg.append(0)
    msg += struct.pack("<Q", ml)

    s = [7, 12, 17, 22] * 4 + [5, 9, 14, 20] * 4 + [4, 11, 16, 23] * 4 + [6, 10, 15, 21] * 4
    k = [int(abs(__import__("math").sin(i + 1)) * 4294967296) & 0xFFFFFFFF for i in range(64)]

    a0, b0, c0, d0 = 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476
    for off in range(0, len(msg), 64):
        m = struct.unpack("<16I", bytes(msg[off:off + 64]))
        a, b, c, d = a0, b0, c0, d0
        for i in range(64):
            if i < 16:
                f = (b & c) | (~b & d)
                g = i
            elif i < 32:
                f = (d & b) | (~d & c)
                g = (5 * i + 1) % 16
            elif i < 48:
                f = b ^ c ^ d
                g = (3 * i + 5) % 16
            else:
                f = c ^ (b | (~d & 0xFFFFFFFF))
                g = (7 * i) % 16
            f = (f + a + k[i] + m[g]) & 0xFFFFFFFF
            a, d, c, b = d, c, b, (b + ((f << s[i]) | (f >> (32 - s[i])))) & 0xFFFFFFFF
        a0 = (a0 + a) & 0xFFFFFFFF
        b0 = (b0 + b) & 0xFFFFFFFF
        c0 = (c0 + c) & 0xFFFFFFFF
        d0 = (d0 + d) & 0xFFFFFFFF
    return struct.pack("<4I", a0, b0, c0, d0)


# ---------------------------------------------------------------- AES-256 解密

_SBOX_HEX = (
    "637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0"
    "b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b275"
    "09832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cf"
    "d0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2"
    "cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdb"
    "e0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08"
    "ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9e"
    "e1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16"
)

_SBOX = [int(_SBOX_HEX[i:i + 2], 16) for i in range(0, 512, 2)]
_INV = [0] * 256
for _i, _v in enumerate(_SBOX):
    _INV[_v] = _i


def _gmul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return p


_M9 = [_gmul(x, 9) for x in range(256)]
_M11 = [_gmul(x, 11) for x in range(256)]
_M13 = [_gmul(x, 13) for x in range(256)]
_M14 = [_gmul(x, 14) for x in range(256)]


def _round_keys(key):
    """AES-256 密钥扩展, 返回 15 组 16 字节轮密钥。"""
    nk, nr = 8, 14
    w = [[key[4 * i + j] for j in range(4)] for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        t = list(w[i - 1])
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[x] for x in t]
            t[0] ^= rcon
            rcon = (rcon << 1) ^ 0x1B if rcon & 0x80 else rcon << 1
        elif i % nk == 4:
            t = [_SBOX[x] for x in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    rks = []
    for r in range(nr + 1):
        k = []
        for c in range(4):
            k.extend(w[4 * r + c])
        rks.append(k)
    return rks


_RS = (0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3)


def _decrypt_block(blk, rks):
    s = [blk[i] ^ rks[14][i] for i in range(16)]
    for rnd in range(13, 0, -1):
        t = [_INV[s[i]] for i in _RS]
        t = [t[i] ^ rks[rnd][i] for i in range(16)]
        o = [0] * 16
        for c in range(4):
            a0, a1, a2, a3 = t[4 * c], t[4 * c + 1], t[4 * c + 2], t[4 * c + 3]
            o[4 * c] = _M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3]
            o[4 * c + 1] = _M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3]
            o[4 * c + 2] = _M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3]
            o[4 * c + 3] = _M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]
        s = o
    t = [_INV[s[i]] for i in _RS]
    return [t[i] ^ rks[0][i] for i in range(16)]


def aes_cbc_decrypt(key, iv, data):
    rks = _round_keys(list(key))
    out = []
    prev = list(iv)
    for off in range(0, len(data) - 15, 16):
        blk = list(data[off:off + 16])
        dec = _decrypt_block(blk, rks)
        out.extend([dec[j] ^ prev[j] for j in range(16)])
        prev = blk
    if out:
        pad = out[-1]
        if 1 <= pad <= 16:
            out = out[:-pad]
    try:
        return bytes(bytearray(out))
    except Exception:
        return b"".join([chr(x) for x in out])


def evp_bytes_to_key(pw, salt, need=48):
    """EVP_BytesToKey(MD5, 1 round) -- 与 CryptoJS 口令模式一致。"""
    d = b""
    prev = b""
    while len(d) < need:
        prev = _md5(prev + pw + salt)
        d += prev
    return d[:need]


# ---------------------------------------------------------------- 本地中转

class _Relay(object):
    """极简本地 HTTP 服务, 用于把 m3u8 里的相对分片绝对化。"""

    def __init__(self, spider):
        self.spider = spider
        self.sock = None
        self.port = 0
        self._lock = threading.Lock()

    def ensure(self):
        if self.port:
            return self.port
        with self._lock:
            if self.port:
                return self.port
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind(("127.0.0.1", 0))
            s.listen(32)
            self.sock = s
            self.port = s.getsockname()[1]
            t = threading.Thread(target=self._loop)
            t.setDaemon(True)
            t.start()
            return self.port

    def _loop(self):
        while True:
            try:
                conn, _ = self.sock.accept()
            except Exception:
                return
            try:
                th = threading.Thread(target=self._handle, args=(conn,))
                th.setDaemon(True)
                th.start()
            except Exception:
                try:
                    conn.close()
                except Exception:
                    pass

    def _handle(self, conn):
        try:
            conn.settimeout(20)
            raw = b""
            while b"\r\n\r\n" not in raw and len(raw) < 65536:
                chunk = conn.recv(4096)
                if not chunk:
                    break
                raw += chunk
            first = raw.split(b"\r\n")[0].decode("latin-1")
            parts = first.split(" ")
            target = parts[1] if len(parts) > 1 else "/"
            body, mime, code = self.spider._relay_dispatch(target)
            head = "HTTP/1.1 %d OK\r\nContent-Type: %s\r\n" \
                   "Content-Length: %d\r\nAccess-Control-Allow-Origin: *\r\n" \
                   "Connection: close\r\n\r\n" % (code, mime, len(body))
            conn.sendall(_to_bytes(head) + body)
        except Exception:
            pass
        finally:
            try:
                conn.close()
            except Exception:
                pass


# ---------------------------------------------------------------- Spider

class Spider(object):

    HOST = "https://theporny.com"
    APP = "theporny.com"
    VER = "260901"
    PASS = b"xxx"

    # 2026-11-13 多轮实测：luchu/madou/tianmtv 响应较稳定；只调整镜像
    # 优先级，不减少重试、不缩短超时，完整召回流程与 v3 相同。
    GATES = [
        "https://v2.luchu.org",
        "https://v2.madou.ws",
        "https://v2.tianmtv.com",
        "https://v2.cdn199.com",
        "https://v2.papapa.biz",
        "https://v2.kekecdn.net",
    ]

    UA = ("Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 "
          "(KHTML, like Gecko) Chrome/122.0.0.0 Mobile Safari/537.36")

    SEARCH_FIELDS = ("title", "title_en", "keywords_gem", "keywords", "videoType", "user")
    # 多关键词时不允许某个词只命中上传者/来源 user；单关键词沿用 v3 全字段召回。
    SEARCH_MULTI_FIELDS = ("title", "title_en", "keywords_gem", "keywords", "videoType")
    SEARCH_PAGE_SIZE = 24
    SEARCH_CACHE_TTL = 900
    SEARCH_CACHE_MAX = 8
    SEARCH_MAX_REMOTE_PAGES = 60
    SEARCH_FETCH_ROUNDS = 2
    SEARCH_MULTI_FETCH_ROUNDS = 2
    SEARCH_TOKEN_VARIANTS_MAX = 8
    SEARCH_REMOTE_STREAMS_MAX = 12
    SEARCH_AMBIGUOUS_VARIANTS_MAX = 4
    SEARCH_CODE_RE = re.compile(r"^([A-Za-z][A-Za-z0-9]*?)[\s._:/#-]*(\d+)$")
    SEARCH_CODE_ANY_RE = re.compile(r"(?<![A-Za-z0-9])([A-Za-z][A-Za-z0-9]*?)[\s._:/#-]*(\d+)(?![A-Za-z0-9])")

    # 实测有独立数据返回的分类 (type 值由站点前端硬编码, 已逐个核对)
    CATS = [
        ("hot", u"热门"),
        ("recent", u"最近更新"),
        ("high", u"高清"),
        ("japan", u"日本AV"),
        ("west", u"欧美风尚"),
        ("swag", u"台湾SWAG"),
        ("banana", u"汝工作室"),
        ("pissvids", u"欧美VIP"),
        ("home_91_8", u"91精选"),
        ("home_vip_8", u"国产制片厂"),
        ("home_hot_8", u"国产自拍"),
        ("home_japan_8", u"日本精选"),
        ("home_west_8", u"欧美精选"),
        ("home_high_8", u"站长推荐"),
        ("home_swag_8", u"SWAG全辑"),
        ("home_banana_8", u"汝工作室精选"),
        ("home_pissvids_8", u"欧美VIP精选"),
    ]

    def __init__(self):
        self.s = None
        self.session = None
        self.sess = None
        self.extend = {}
        self.base = self.GATES[0]
        self._gates = list(self.GATES)
        self.gate_idx = 0
        self.interval = 1.0
        self.img_relay = False
        self.use_proxy = True
        self._last_req = 0.0
        self._relay = _Relay(self)
        self._cache = {}
        self._search_cache = {}
        self._req_lock = threading.Lock()
        self._search_lock = threading.RLock()

    # -------------------------------------------------- 生命周期

    def getDependence(self):
        return []

    def init(self, extend=""):
        self.extend = self._parse_ext(extend)
        self.base = self.GATES[0]
        if self.extend.get("base"):
            b = str(self.extend["base"]).strip().rstrip("/")
            if not b.startswith("http"):
                b = "https://" + b
            self.base = b
        gates = []
        for gate in [self.base] + list(self.GATES):
            gate = _to_text(gate).strip().rstrip("/")
            if gate and gate not in gates:
                gates.append(gate)
        self._gates = gates
        self.gate_idx = 0
        try:
            self.interval = float(self.extend.get("interval", 1.0))
        except Exception:
            self.interval = 1.0
        if self.interval < 0:
            self.interval = 0.0
        self.img_relay = str(self.extend.get("img", "direct")).lower() == "relay"
        self.use_proxy = str(self.extend.get("proxy", "1")).lower() not in ("0", "false", "no")
        self._build_session()

    def _parse_ext(self, extend):
        if isinstance(extend, dict):
            return dict(extend)
        d = {}
        if isinstance(extend, (list, tuple)) and extend:
            extend = extend[0]
        if not isinstance(extend, text_type):
            return d
        s = extend.strip()
        if not s:
            return d
        if s.startswith("{"):
            try:
                v = json.loads(s)
                if isinstance(v, dict):
                    return v
            except Exception:
                return d
        for part in s.split("|"):
            part = part.strip()
            if not part:
                continue
            if part.startswith("http") and "base" not in d:
                d["base"] = part
            elif "=" in part:
                k, v = part.split("=", 1)
                d[k.strip()] = v.strip()
        return d

    def _build_session(self):
        if requests is None:
            self.s = self.session = self.sess = None
            return
        try:
            s = requests.Session()
            s.headers.update(self._headers())
            self.s = self.session = self.sess = s
        except Exception:
            self.s = self.session = self.sess = None

    def _headers(self):
        return {
            "User-Agent": self.UA,
            "Content-Type": "application/json",
            "Accept": "application/json, text/plain, */*",
            "Origin": self.HOST,
            "Referer": self.HOST + "/",
        }

    def destroy(self):
        self._cache = {}
        self._search_cache = {}
        return None

    def manualVideoCheck(self):
        return False

    def action(self, action):
        return {}

    def isVideoFormat(self, url):
        if not url:
            return False
        u = str(url).lower()
        for k in (".m3u8", ".mp4", ".flv", ".avi", ".mkv", ".ts"):
            if k in u:
                return True
        return False

    # -------------------------------------------------- 网络

    def _throttle(self):
        if self.interval <= 0:
            return
        with self._req_lock:
            gap = time.time() - self._last_req
            if gap < self.interval:
                time.sleep(self.interval - gap)
            self._last_req = time.time()

    def _post(self, path, tries=3, extra=None):
        body = {
            "url": path,
            "app": self.APP,
            "version": self.VER,
            "deviceInfo": {},
            "uuid": "novalue",
            "theLink": "novaluenull",
            "isStandalone": False,
        }
        # 搜索接口要求 page/keywords/筛选项位于 /js 的顶层请求体，
        # 不能拼进 body["url"]；后者会被服务端忽略并返回默认列表。
        if isinstance(extra, dict):
            for k, v in extra.items():
                body[k] = v
        payload = json.dumps(body)
        last = None
        gates = self._gates or list(self.GATES)
        try:
            count = min(max(int(tries), 1), len(gates))
        except Exception:
            count = min(3, len(gates))
        for i in range(count):
            idx = (self.gate_idx + i) % len(gates)
            base = gates[idx]
            try:
                self._throttle()
                txt = self._http_post(base + "/js", payload)
                if not txt:
                    continue
                try:
                    obj = json.loads(txt)
                except Exception:
                    continue
                if isinstance(obj, dict) and "r" in obj:
                    self.gate_idx = idx
                    return self._decrypt(obj["r"])
                if isinstance(obj, dict) and obj.get("blocked"):
                    last = "blocked"
                    continue
                return obj
            except Exception as e:
                last = e
                continue
        if last is not None:
            return None
        return None

    def _http_post(self, url, payload):
        data = _to_bytes(payload)
        if self.s is not None:
            r = self.s.post(url, data=data, timeout=25)
            if r.status_code != 200:
                raise IOError("http %s" % r.status_code)
            return _to_text(r.content)
        req = Request(url, data=data, headers=self._headers())
        resp = urlopen(req, timeout=25)
        return _to_text(resp.read())

    def _get(self, url, referer=None, tries=2):
        """取原始文件 (m3u8 / 图片)。"""
        for i in range(tries):
            try:
                self._throttle()
                hdr = {"User-Agent": self.UA}
                if referer:
                    hdr["Referer"] = referer
                if self.s is not None:
                    r = self.s.get(url, headers=hdr, timeout=25)
                    if r.status_code != 200:
                        raise IOError("http %s" % r.status_code)
                    return r.content
                req = Request(url, headers=hdr)
                return urlopen(req, timeout=25).read()
            except Exception as e:
                # 有些 CDN 会给出偏大的 Content-Length, 读半截报错但数据已到手
                part = getattr(e, "partial", None)
                if part:
                    return part
                if i == tries - 1:
                    return None
        return None

    def _decrypt(self, raw):
        try:
            b = base64.b64decode(_to_bytes(raw))
        except (binascii.Error, ValueError):
            return None
        if not b.startswith(b"Salted__") or len(b) < 32:
            try:
                return json.loads(_to_text(b))
            except Exception:
                return None
        salt = b[8:16]
        ct = b[16:]
        material = evp_bytes_to_key(self.PASS, salt, 48)
        pt = aes_cbc_decrypt(material[:32], material[32:48], ct)
        try:
            return json.loads(_to_text(pt))
        except Exception:
            return None

    # -------------------------------------------------- 数据整形

    def _pic(self, vid, item=None):
        thumbs = []
        if isinstance(item, dict):
            thumbs = item.get("thumbnails") or item.get("thumbNails") or []
        if thumbs:
            pic = self._fix_url(thumbs[0])
        else:
            pic = "https://tp.helloye.com/%s.jpg" % vid
        if self.img_relay:
            return self._relay_url("img", pic)
        return pic

    def _fix_url(self, u):
        if not u:
            return ""
        u = _to_text(u).strip()
        if u.startswith("//"):
            return "https:" + u
        if u.startswith("http"):
            return u
        return urljoin(self.HOST + "/", u)

    # 未成年条目一律不进列表 (年龄 <18 的直接丢; 明确写 18/19 岁的不误杀)
    _AGE_RE = re.compile(r"(\d{1,2})\s*岁")

    _MINOR_WORDS = (u"未成年", u"幼女", u"女童", u"小学生", u"初中生", u"初一", u"初二",
                    u"初三", u"儿童色情", u"萝莉幼", u"萝莉妹")

    def _is_minor(self, title):
        t = _to_text(title or "")
        if not t:
            return False
        for m in self._AGE_RE.finditer(t):
            try:
                if int(m.group(1)) < 18:
                    return True
            except Exception:
                pass
        for w in self._MINOR_WORDS:
            if w in t:
                return True
        return False

    def _video_item(self, v):
        try:
            vid = _to_text(v.get("id") or v.get("vId") or "")
            name = _to_text(v.get("title") or "")
            if not name:
                name = _to_text(v.get("title_en") or vid)
            if self._is_minor(name) or self._is_minor(_to_text(v.get("title_en") or "")):
                return None
            return {
                "vod_id": vid,
                "vod_name": name,
                "vod_pic": self._pic(vid, v),
                "vod_remarks": _to_text(v.get("size") or v.get("durationStr") or ""),
            }
        except Exception:
            return None

    def _unwrap(self, data):
        """兼容 服务端可能返回 {list:[...]} 或 裸数组。"""
        if isinstance(data, dict):
            for k in ("list", "videos", "data", "sevenVideos", "result"):
                if isinstance(data.get(k), list):
                    return data[k]
            return []
        if isinstance(data, list):
            return data
        return []

    # -------------------------------------------------- 13 接口

    def homeContent(self, filter=None):
        cats = [{"type_id": t, "type_name": n} for t, n in self.CATS]
        return {"class": cats, "filters": {}}

    def homeVideoContent(self):
        lst = []
        for t, _n in self.CATS[:4]:
            for it in self._list(t, 1):
                lst.append(it)
        return {"list": lst}

    def categoryContent(self, tid, pg=1, filter=None, extend=None):
        tid = _to_text(tid or self.CATS[0][0])
        try:
            pg = int(str(pg))
        except Exception:
            pg = 1
        if pg < 1:
            pg = 1
        lst = self._list(tid, pg)
        return {"list": lst, "page": pg, "pagecount": pg + 1 if lst else pg,
                "limit": 24, "total": len(lst)}

    def _list(self, tid, pg):
        data = self._post("/sevenVideos?page=%d&type=%s" % (pg, tid))
        raw = self._unwrap(data)
        out = []
        seen = set()
        for v in raw:
            if not isinstance(v, dict):
                continue
            it = self._video_item(v)
            if not it or not it["vod_id"]:
                continue
            if it["vod_id"] in seen:
                continue
            seen.add(it["vod_id"])
            out.append(it)
        return out

    def detailContent(self, ids):
        vid = ids[0] if isinstance(ids, (list, tuple)) and ids else ids
        vid = _to_text(vid or "")
        vid = vid.split("|")[0].split("$")[0]
        if not vid:
            return {"list": []}
        d = self._detail(vid)
        if not d:
            return {"list": []}
        name = _to_text(d.get("title") or d.get("title_en") or vid)
        if self._is_minor(name) or self._is_minor(_to_text(d.get("title_en") or "")):
            return {"list": []}
        pics = d.get("thumbnails") or []
        pic = self._pic(vid, d) if pics else "https://tp.helloye.com/%s.jpg" % vid
        lines = d.get("m3u8s") or []
        if not lines and d.get("m3u8"):
            lines = [d["m3u8"]]
        froms = []
        urls = []
        if len(lines) > 1:
            for i, u in enumerate(lines):
                froms.append(u"线路%d" % (i + 1))
                urls.append(u"正片$%s" % vid)
        else:
            froms.append(u"theporny")
            urls.append(u"正片$%s" % vid)
        cont = u"片名: %s\n主演/来源: %s\n时长: %s\n大小: %s\n播放: %s\n时间: %s" % (
            name,
            _to_text(d.get("user") or ""),
            _to_text(d.get("durationStr") or ""),
            _to_text(d.get("size") or ""),
            _to_text(d.get("views") or ""),
            _to_text(d.get("time") or ""),
        )
        return {"list": [{
            "vod_id": vid,
            "vod_name": name,
            "vod_pic": pic,
            "vod_content": cont,
            "vod_play_from": "$$$".join(froms),
            "vod_play_url": "$$$".join(urls),
        }]}

    def _detail(self, vid, ttl=120):
        now = time.time()
        c = self._cache.get(vid)
        if c and now - c[0] < ttl:
            return c[1]
        d = self._post("/sevenVideos/" + quote(vid))
        if isinstance(d, dict) and (d.get("m3u8s") or d.get("title")):
            self._cache[vid] = (now, d)
            return d
        return d if isinstance(d, dict) else None

    # -------------------------------------------------- 搜索

    def _normalize_spaces(self, text):
        return u" ".join(_to_text(text or "").strip().split())

    def _to_simplified(self, text):
        """字符级简繁统一只用于搜索比较；不改展示标题。"""
        return u"".join(_T2S_MAP.get(ch, ch) for ch in _to_text(text or ""))

    def _to_traditional(self, text):
        return u"".join(_S2T_MAP.get(ch, ch) for ch in _to_text(text or ""))

    def _canonical_code(self, text):
        """通用“字母前缀 + 可选分隔符 + 数字”归一，不维护番号白名单。"""
        value = self._normalize_spaces(text)
        match = self.SEARCH_CODE_RE.match(value)
        if not match:
            return None
        return _fold_text(match.group(1)) + u"-" + match.group(2)

    def _parse_search_tokens(self, key):
        """先识别整条番号，再按空格拆成必须全部命中的逻辑词。"""
        value = self._normalize_spaces(key)
        if not value:
            return []
        code = self._canonical_code(value)
        raw_tokens = [value] if code else value.split(u" ")
        tokens = []
        for raw in raw_tokens:
            raw = raw.strip()
            if not raw:
                continue
            token_code = self._canonical_code(raw)
            canonical = token_code or self._to_simplified(_fold_text(raw)).strip()
            if not canonical:
                continue
            token = {"raw": raw, "canonical": canonical,
                     "is_code": bool(token_code)}
            token["variants"] = self._token_variants(token)
            tokens.append(token)
        return tokens

    def _case_variants(self, text):
        root = _fold_text(text).strip()
        if not root:
            return []
        has_ascii_letter = any((u"a" <= ch <= u"z" or u"A" <= ch <= u"Z")
                               for ch in root)
        choices = (root, root.title(), root.upper()) if has_ascii_letter else (root,)
        out = []
        for item in choices:
            if item and item not in out:
                out.append(item)
        return out

    def _traditional_variants(self, simplified):
        """默认繁体加受控歧义变体；不做无上限笛卡尔积。"""
        base = self._to_traditional(simplified)
        out = [base] if base else []
        for pos, ch in enumerate(simplified):
            choices = _S2T_AMBIG.get(ch, u"")
            if not choices:
                continue
            for replacement in choices:
                item = base[:pos] + replacement + base[pos + 1:]
                if item and item not in out:
                    out.append(item)
                    if len(out) >= self.SEARCH_AMBIGUOUS_VARIANTS_MAX:
                        return out
        return out

    def _token_variants(self, token):
        canonical = token["canonical"]
        seeds = []
        if token.get("is_code"):
            prefix, digits = canonical.rsplit(u"-", 1)
            # 网站标题统一使用连字符；固定由规范键生成，确保输入形式不影响结果。
            seeds = [prefix + u"-" + digits]
        else:
            simplified = self._to_simplified(canonical)
            seeds = [simplified]
            for item in self._traditional_variants(simplified):
                if item not in seeds:
                    seeds.append(item)

        out = []
        for seed in seeds:
            for item in self._case_variants(seed):
                if item and item not in out:
                    out.append(item)
                    if len(out) >= self.SEARCH_TOKEN_VARIANTS_MAX:
                        return out
        return out

    def _search_variants(self, key):
        """兼容旧测试入口；返回解析后全部远程查询流。"""
        out = []
        for token in self._parse_search_tokens(key):
            for term in token["variants"]:
                if term not in out:
                    out.append(term)
        return out

    def _canonical_match_text(self, text):
        return self._to_simplified(_fold_text(text)).strip()

    def _normalize_codes_in_text(self, text):
        def replace(match):
            return _fold_text(match.group(1)) + u"-" + match.group(2)
        return self.SEARCH_CODE_ANY_RE.sub(replace, text)

    def _search_match_quality(self, text, token):
        """返回 (匹配级别, 位置)；每个逻辑词独立做大小写、简繁和番号归一。"""
        hay = self._canonical_match_text(text)
        if not hay or not token:
            return None
        needle = token["canonical"] if isinstance(token, dict) else _to_text(token)
        needle = self._canonical_match_text(needle)
        if isinstance(token, dict) and token.get("is_code"):
            hay = self._normalize_codes_in_text(hay)
            needle = self._normalize_codes_in_text(needle)
        if not needle:
            return None
        if hay == needle:
            return (0, 0)
        best = None
        start = 0
        separators = u" \t\r\n-_.:/#"
        while True:
            pos = hay.find(needle, start)
            if pos < 0:
                break
            end = pos + len(needle)
            prev_boundary = pos == 0 or not _ascii_alnum(hay[pos - 1])
            next_boundary = end == len(hay) or not _ascii_alnum(hay[end])
            j = end
            while j < len(hay) and hay[j] in separators:
                j += 1
            numeric_suffix = j < len(hay) and _ascii_digit(hay[j])
            if prev_boundary and numeric_suffix:
                tier = 1
            elif prev_boundary and next_boundary:
                tier = 2 if pos == 0 else 3
            elif prev_boundary:
                tier = 4 if pos == 0 else 5
            else:
                tier = 6
            candidate = (tier, pos)
            if best is None or candidate < best:
                best = candidate
            start = pos + 1
        return best

    def _search_field_value(self, row, field):
        value = row.get(field)
        if isinstance(value, (list, tuple)):
            return u" ".join(_to_text(x) for x in value)
        if isinstance(value, dict):
            return u" ".join(_to_text(value[k]) for k in sorted(value))
        return _to_text(value or "")

    def _search_token_rank(self, row, token, fields=None):
        best = None
        fields = fields or self.SEARCH_FIELDS
        for field_index, field in enumerate(fields):
            quality = self._search_match_quality(self._search_field_value(row, field), token)
            if quality is None:
                continue
            candidate = (quality[0], field_index, quality[1])
            if best is None or candidate < best:
                best = candidate
        return best

    def _search_rank(self, row, tokens):
        """所有逻辑词必须命中；最差词优先决定排序，再比较整体质量。"""
        if not isinstance(tokens, (list, tuple)):
            tokens = [{"canonical": _to_text(tokens), "is_code": False}]
        ranks = []
        fields = self.SEARCH_MULTI_FIELDS if len(tokens) > 1 else self.SEARCH_FIELDS
        for token in tokens:
            rank = self._search_token_rank(row, token, fields)
            if rank is None:
                return None
            ranks.append(rank)
        worst = max(ranks)
        tiers = sum(item[0] for item in ranks)
        fields = sum(item[1] for item in ranks)
        positions = sum(item[2] for item in ranks)
        return (worst[0], tiers, fields, positions) + tuple(ranks)

    def _canonical_search_key(self, tokens):
        return u" ".join(token["canonical"] for token in tokens)

    def _new_search_state(self, key):
        tokens = self._parse_search_tokens(key)
        variants = []
        if len(tokens) > 1:
            # 多词必须作为 + 分隔的组合请求。服务端对每个词仍大小写敏感；
            # 用广度优先枚举受限笛卡尔积，让每个词的简繁/大小写独立组合，
            # 同时由 SEARCH_REMOTE_STREAMS_MAX 限制总请求流数量。
            lengths = [len(token["variants"]) for token in tokens]
            if lengths and all(lengths):
                first = tuple(0 for _token in tokens)
                queue = [first]
                seen_indexes = set([first])
                while queue and len(variants) < self.SEARCH_REMOTE_STREAMS_MAX:
                    indexes = queue.pop(0)
                    variants.append(tuple(tokens[pos]["variants"][indexes[pos]]
                                          for pos in range(len(tokens))))
                    for pos in range(len(tokens)):
                        if indexes[pos] + 1 >= lengths[pos]:
                            continue
                        following = list(indexes)
                        following[pos] += 1
                        following = tuple(following)
                        if following not in seen_indexes:
                            seen_indexes.add(following)
                            queue.append(following)
        else:
            for token in tokens:
                for term in token["variants"]:
                    stream = (term,)
                    if stream not in variants and len(variants) < self.SEARCH_REMOTE_STREAMS_MAX:
                        variants.append(stream)
        now = time.time()
        return {
            "key": self._canonical_search_key(tokens),
            "tokens": tokens,
            "variants": variants,
            "next_page": dict((stream, 1) for stream in variants),
            "exhausted": dict((stream, False) for stream in variants),
            "failures": dict((stream, 0) for stream in variants),
            "candidates": {},
            "emitted": set(),
            "pages": [],
            "seq": 0,
            "created": now,
            "access": now,
        }

    def _get_search_state(self, key):
        now = time.time()
        expired = [cache_key for cache_key, value in self._search_cache.items()
                   if now - value.get("access", now) > self.SEARCH_CACHE_TTL]
        for cache_key in expired:
            self._search_cache.pop(cache_key, None)
        parsed = self._parse_search_tokens(key)
        canonical = self._canonical_search_key(parsed)
        # 规范键直接作缓存索引；Python 2/3 的 Unicode 字典键均可用。
        cache_key = canonical
        state = self._search_cache.get(cache_key)
        if state is None:
            if len(self._search_cache) >= self.SEARCH_CACHE_MAX:
                oldest = min(self._search_cache,
                             key=lambda k: self._search_cache[k].get("access", 0))
                self._search_cache.pop(oldest, None)
            state = self._new_search_state(key)
            self._search_cache[cache_key] = state
        state["access"] = now
        return state

    def _request_search_page(self, term, page):
        params = {
            "page": page,
            "keywords": term,
            "filterCategory": "all",
            "filterTimeInDays": "all",
            "filterViews": "all",
            "filterDurationInMins": "all",
            "sortBy": "time",
            "keywordLogic": "and",
        }
        data = self._post("/searchSevenVideos", extra=params)
        if not isinstance(data, (dict, list)):
            return None
        return self._unwrap(data)

    def _request_search_terms_page(self, terms, page):
        """站点以 + 分隔逻辑词；空格会被当成连续短语而返回空列表。"""
        query = u"+".join(_to_text(term) for term in terms if term)
        if not query:
            return []
        return self._request_search_page(query, page)

    def _ingest_search_rows(self, state, rows):
        for row in rows:
            if not isinstance(row, dict):
                continue
            vid = _to_text(row.get("id") or row.get("vId") or "")
            if not vid or vid in state["emitted"]:
                continue
            title = _to_text(row.get("title") or "")
            title_en = _to_text(row.get("title_en") or "")
            if self._is_minor(title) or self._is_minor(title_en):
                continue
            # 组合请求已经由服务端筛出同时命中的记录；这里仍做一次本地 AND 复核。
            rank = self._search_rank(row, state["tokens"])
            if rank is None:
                continue
            old = state["candidates"].get(vid)
            if old is None:
                state["seq"] += 1
                state["candidates"][vid] = {
                    "row": row,
                    "rank": rank,
                    "seq": state["seq"],
                }
            elif rank < old["rank"]:
                old["row"] = row
                old["rank"] = rank

    def _search_active(self, state):
        return any(not state["exhausted"].get(stream, True)
                   for stream in state["variants"])

    def _fetch_search_round(self, state):
        attempted = 0
        succeeded = 0
        for stream in state["variants"]:
            if state["exhausted"].get(stream):
                continue
            terms = stream
            page = state["next_page"].get(stream, 1)
            if page > self.SEARCH_MAX_REMOTE_PAGES:
                state["exhausted"][stream] = True
                continue
            attempted += 1
            rows = (self._request_search_terms_page(terms, page) if len(terms) > 1
                    else self._request_search_page(terms[0], page))
            if rows is None:
                state["failures"][stream] = state["failures"].get(stream, 0) + 1
                continue
            succeeded += 1
            state["failures"][stream] = 0
            state["next_page"][stream] = page + 1
            self._ingest_search_rows(state, rows)
            if len(rows) < self.SEARCH_PAGE_SIZE:
                state["exhausted"][stream] = True
        return attempted, succeeded

    def _pending_search_candidates(self, state):
        pending = []
        for vid, candidate in state["candidates"].items():
            if vid not in state["emitted"]:
                pending.append(candidate)
        return pending

    def _build_next_search_page(self, state):
        rounds = 0
        max_rounds = (self.SEARCH_MULTI_FETCH_ROUNDS if len(state["tokens"]) > 1
                      else self.SEARCH_FETCH_ROUNDS)
        while True:
            pending = self._pending_search_candidates(state)
            strong = sum(1 for item in pending if item["rank"][0] <= 3)
            active = self._search_active(state)
            if len(pending) >= self.SEARCH_PAGE_SIZE and strong >= self.SEARCH_PAGE_SIZE:
                break
            if not active or rounds >= max_rounds:
                break
            # 单词搜索沿用 v2 的限流策略；多词交集允许继续向深页渐进查找。
            if (len(state["tokens"]) == 1 and rounds > 0 and
                    len(pending) >= self.SEARCH_PAGE_SIZE and strong == 0):
                break
            attempted, succeeded = self._fetch_search_round(state)
            rounds += 1
            if attempted == 0:
                break
            if succeeded == 0 and rounds >= max_rounds:
                break

        pending = self._pending_search_candidates(state)
        pending.sort(key=lambda item: item["rank"] + (item["seq"],))
        selected = pending[:self.SEARCH_PAGE_SIZE]
        if not selected:
            return []
        rows = []
        for item in selected:
            row = item["row"]
            vid = _to_text(row.get("id") or row.get("vId") or "")
            if not vid or vid in state["emitted"]:
                continue
            state["emitted"].add(vid)
            rows.append(row)
        if rows:
            state["pages"].append(rows)
        return rows

    def _ensure_search_page(self, state, page):
        while len(state["pages"]) < page:
            before = len(state["pages"])
            rows = self._build_next_search_page(state)
            if not rows or len(state["pages"]) == before:
                break

    def searchContent(self, key, quick=False, pg="1"):
        key = self._normalize_spaces(key)
        try:
            pg = int(str(pg))
        except Exception:
            pg = 1
        if pg < 1:
            pg = 1
        if not key:
            return {"list": [], "page": pg, "pagecount": pg, "limit": self.SEARCH_PAGE_SIZE,
                    "total": 0}

        with self._search_lock:
            state = self._get_search_state(key)
            if not state["tokens"] or not state["variants"]:
                return {"list": [], "page": pg, "pagecount": pg,
                        "limit": self.SEARCH_PAGE_SIZE, "total": 0}
            self._ensure_search_page(state, pg)
            rows = state["pages"][pg - 1] if pg <= len(state["pages"]) else []
            out = []
            seen = set()
            for row in rows:
                item = self._video_item(row)
                if not item or not item["vod_id"] or item["vod_id"] in seen:
                    continue
                seen.add(item["vod_id"])
                out.append(item)

            pending_count = len(self._pending_search_candidates(state))
            active = self._search_active(state)
            has_more = bool(out) and (pending_count > 0 or active)
            known_pages = len(state["pages"])
            pagecount = max(pg, known_pages + (1 if has_more else 0))
            total = len(state["emitted"]) + pending_count + (1 if active else 0)
            state["access"] = time.time()
            return {"list": out, "page": pg, "pagecount": pagecount,
                    "limit": self.SEARCH_PAGE_SIZE, "total": total}

    def searchContentPage(self, key, quick=False, pg="1", size="24"):
        """兼容会单独调用分页搜索入口的影视 APP；站点服务端页长固定为 24。"""
        return self.searchContent(key, quick, pg)

    def playerContent(self, flag, ids, vipFlags=None):
        vid = ids[0] if isinstance(ids, (list, tuple)) and ids else ids
        vid = _to_text(vid or "").split("$")[-1].split("|")[0]
        url = self._play_url(vid)
        header = {
            "User-Agent": self.UA,
            "Referer": self.HOST + "/",
            "Origin": self.HOST,
        }
        if not url:
            return {"parse": 0, "jx": 0, "playUrl": "", "url": "", "header": header}
        if self.use_proxy:
            return {"parse": 0, "jx": 0, "playUrl": "", "url": self._relay_url("m3u8", url),
                    "header": header, "format": "application/x-mpegURL"}
        return {"parse": 0, "jx": 0, "playUrl": "", "url": url,
                "header": header, "format": "application/x-mpegURL"}

    def _play_url(self, vid):
        d = self._detail(vid, ttl=60)
        if not d:
            return ""
        lines = d.get("m3u8s") or []
        if not lines and d.get("m3u8"):
            lines = [d["m3u8"]]
        for u in lines:
            u = self._fix_url(u)
            if u:
                return u
        return ""

    # -------------------------------------------------- 本地中转

    def _relay_url(self, kind, target):
        try:
            port = self._relay.ensure()
        except Exception:
            return target
        raw = base64.b64encode(_to_bytes(target))
        raw = raw.replace(b"+", b"-").replace(b"/", b"_").rstrip(b"=")
        return "http://127.0.0.1:%d/%s?u=%s" % (port, kind, _to_text(raw))

    def _relay_dispatch(self, target):
        try:
            q = target.split("?", 1)[1] if "?" in target else ""
            kind = "m3u8"
            if target.startswith("/img"):
                kind = "img"
            val = ""
            for kv in q.split("&"):
                if kv.startswith("u="):
                    val = unquote(kv[2:])
                    break
            if not val:
                return b"no url", "text/plain", 400
            pad = "=" * (-len(val) % 4)
            real = _to_text(base64.b64decode(_to_bytes(val.replace("-", "+").replace("_", "/") + pad)))
            if kind == "img":
                data = self._get(real, referer=self.HOST + "/")
                if not data:
                    return b"", "image/jpeg", 404
                mime = "image/jpeg"
                if data[:8].startswith(b"\x89PNG"):
                    mime = "image/png"
                elif data[:4] == b"RIFF":
                    mime = "image/webp"
                return data, mime, 200
            raw = self._get(real, referer=self.HOST + "/")
            if not raw:
                return b"", "application/vnd.apple.mpegurl", 502
            clean = self._clean_m3u8(_to_text(raw), real)
            return _to_bytes(clean), "application/vnd.apple.mpegurl", 200
        except Exception:
            return b"", "application/vnd.apple.mpegurl", 500

    def _clean_m3u8(self, text, base):
        out = []
        for line in text.splitlines():
            s = line.strip()
            if not s:
                out.append(line)
                continue
            if s.startswith("#"):
                # 只动 #EXT-X-KEY / #EXT-X-MAP 里的 URI, 其余控制标签一律原样保留
                if "URI=" in s:
                    s = re.sub(r'URI="([^"]+)"',
                               lambda m: 'URI="%s"' % urljoin(base, m.group(1)), s)
                out.append(s)
                continue
            out.append(urljoin(base, s))
        return "\n".join(out)

    def localProxy(self, param):
        try:
            if isinstance(param, text_type):
                try:
                    param = json.loads(param)
                except Exception:
                    param = {}
            if not isinstance(param, dict):
                param = {}
            target = param.get("url") or param.get("path") or ""
            if not target:
                return [404, "text/plain", b"Not Found", {}]
            body, mime, code = self._relay_dispatch(_to_text(target))
            return [code, mime, body, {"Access-Control-Allow-Origin": "*"}]
        except Exception:
            return [500, "text/plain", b"error", {}]


# ---------------------------------------------------------------- CLI 自测

def _main(argv):
    import sys

    sp = Spider()
    sp.init("")
    cmd = argv[1] if len(argv) > 1 else "nav"
    if cmd == "nav":
        for c in sp.homeContent().get("class", []):
            print("%-18s %s" % (c["type_id"], c["type_name"]))
    elif cmd == "list":
        tid = argv[2] if len(argv) > 2 else "hot"
        pg = argv[3] if len(argv) > 3 else "1"
        r = sp.categoryContent(tid, pg)
        print("page=%s n=%d" % (r["page"], len(r["list"])))
        for v in r["list"][:6]:
            print("  %-14s %s" % (v["vod_id"], v["vod_name"][:44]))
    elif cmd == "detail":
        r = sp.detailContent([argv[2]])
        if r["list"]:
            d = r["list"][0]
            print(d["vod_name"])
            print(d["vod_content"])
            print("play_url:", d["vod_play_url"])
    elif cmd == "play":
        vid = argv[2]
        r = sp.playerContent("", vid, [])
        print("url:", r["url"])
        if not r["url"].startswith("http://127.0.0.1"):
            print("header:", r["header"])
    elif cmd == "search":
        r = sp.searchContent(argv[2] if len(argv) > 2 else u"麻豆", False, "1")
        print("n=%d" % len(r["list"]))
        for v in r["list"][:6]:
            print("  %-14s %s" % (v["vod_id"], v["vod_name"][:44]))
    else:
        print(__doc__)
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(_main(sys.argv))
