"""消息处理模块"""

import asyncio
import base64
import datetime
import html
import io
import os
import random
import re
import sqlite3
import time
import traceback

import jieba
from matplotlib import font_manager as fm
from matplotlib import pyplot as plt
import numpy as np
from PIL import Image, ImageDraw
from wordcloud import WordCloud

from src.utils import (
    MiniCron,
    Module,
    get_error,
    get_group_member_list,
    get_group_name,
    get_record,
    get_stranger_info,
    get_user_name,
    reply_back,
    set_emoji,
    status_ok,
    via
)

class Chat(Module):
    """消息处理模块"""

    ID = "Chat"
    NAME = "消息处理模块"
    HELP = {
        2: [
            "[时间段]词云 | 生成某一时间段的词云",
            "[时间段]复读排行 | 生成某一时间段的复读排行",
            "[时间段]发言排行 | 生成某一时间段的发言排行",
            "为XXX生成[时间段]的词云 | 生成某人某一时间段的词云",
            "词云配色 [配色代码] | 更改词云配色",
            "[QQ账号或昵称]又叫做[称号] | 记录成员的称号",
            "成员列表 | 查看曾有称号记录在案的成员列表和称号",
            "[QQ账号或昵称]曾言道: | 假装有人说过",
            "刚刚撤回了什么 | 查看上一个撤回消息内容",
            "回复表情图片并@机器人(空内容) | 将表情包转化为链接",
            "回复消息并发送💩 | 对回复的消息贴表情💩",
            "回复消息并发送❤️ | 对回复的消息“一键发电”贴表情",
        ],
        1: [
            "(打开|关闭)词云 | 打开或关闭消息记录(默认关闭)",
        ],
    }
    GLOBAL_CONFIG = {
        "database": "data.db",
        "font": "MiSans-Bold.ttf",
        "emoji-font": "NotoEmoji-Bold.ttf",
        "stopwords": "stopwords.txt",
        "qq_data": "/app/QQ"
    }
    CONV_CONFIG = {
        "record": {
            "auto_cron": "",
            "auto_wordcloud": "",
            "auto_statistics": "",
            "enable": False,
            "colormap": "Set2"
        },
        "repeat_record": {
            "enable": False
        },
        "users": {}
    }
    HANDLE_MESSAGE_SENT = True
    AUTO_INIT = True

    def __init__(self, event, auth = 0):
        self.en2cn_dict = {
            "all": "历史", "today": "今天", "yesterday": "昨天", "before_yesterday": "前天",
            "this_week": "本周", "last_week": "上周",
            "this_month": "本月", "last_month": "上个月",
            "this_year": "今年", "last_year": "去年"
        }
        super().__init__(event, auth)
        if self.ID in self.robot.persist_mods:
            return
        self.robot.persist_mods[self.ID] = self
        asyncio.run_coroutine_threadsafe(self.init_task(), self.robot.loop)

    async def init_task(self) -> None:
        """初始化定时任务"""
        # 词云与发言排行统计定时任务
        await asyncio.sleep(5)
        for owner, config in self.config.items():
            if not re.match(r"[ug]\d+", owner):
                continue
            record = config.get("record", {})
            crontab = record.get("auto_cron")
            if not crontab:
                continue
            cron = MiniCron(crontab, lambda o=owner,c=record: self.scheduled_task(o, c), loop=self.robot.loop)
            self.printf(f"已为[{owner}]开启词云与发言排行统计定时任务[{crontab}]")
            asyncio.run_coroutine_threadsafe(cron.run(), self.robot.loop)

    async def scheduled_task(self, owner_id: str, config: dict) -> None:
        """根据配置发送词云与排行统计"""
        try:
            msg = ""
            if gen_type := config["auto_wordcloud"]:
                msg = f"{self.en2cn_dict[gen_type]}统计数据\n"
                rows = self.read_chat(gen_type, owner_id)
                text = "\n".join([r[3] for r in rows if r[3]])
                url = self.generate_wordcloud(text)
                msg += f"[CQ:image,file={url}]"
            if gen_type := config["auto_statistics"]:
                rows = self.read_tally(gen_type, owner_id)
                url = self.generate_statistics(rows)
                msg += f"[CQ:image,file={url}]"
            reply_back(self.robot, owner_id, msg)
        except Exception:
            self.errorf(f"任务执行失败 {traceback.format_exc()}")

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"词云"), success=False)
    def wordcloud(self):
        """词云"""
        date_pattern = "历史|全部|今天|今日|本日|这天|昨天|昨日|前天|前日|本周|这周|此周|这个?礼拜|这个?星期|上周|上个?礼拜|上个?星期|本月|这月|次月|这个月|上个?月|今年|本年|此年|这一?年|去年|上一?年"
        if self.match(r"(开启|启用|打开|记录|启动|关闭|禁用|取消)"):
            if self.auth <= 1:
                self.record_switch()
                return
            else:
                msg = "你没有此操作的权限！"
        elif self.match(r"(主题|颜色|色彩|方案|配色)"):
            self.wordcloud_colormap()
            return
        elif result := self.match(rf"(给|为)?([^\s]*?)?\s?(生成|的)?({date_pattern})?的?词云"):
            if self.config[self.owner_id]["record"]["enable"]:
                gen_type = "all"
                if self.match(r"(今天|今日|本日|这天)"):
                    gen_type = "today"
                elif self.match(r"(昨天|昨日)"):
                    gen_type = "yesterday"
                elif self.match(r"(前天|前日)"):
                    gen_type = "before_yesterday"
                elif self.match(r"(本周|这周|此周|这个?礼拜|这个?星期)"):
                    gen_type = "this_week"
                elif self.match(r"(上周|上个?礼拜|上个?星期)"):
                    gen_type = "last_week"
                elif self.match(r"(本月|这月|次月|这个月)"):
                    gen_type = "this_month"
                elif self.match(r"(上个?月)"):
                    gen_type = "last_month"
                elif self.match(r"(今年|本年|此年|这一?年)"):
                    gen_type = "this_year"
                elif self.match(r"(去年|上一?年)"):
                    gen_type = "last_year"
                cn_type = self.en2cn_dict.get(gen_type, "历史")
                msg = f"正在生成{cn_type}词云..."
                text = ""
                user_name = result.group(2)
                user_id = None
                if user_name:
                    user_id = self.get_uid(user_name)
                    if not user_id and user_name not in self.robot.data.keys():
                        self.reply(f"未检索到关于{user_name}的消息记录")
                        return
                    elif user_name in self.robot.data.keys():
                        rows = self.read_chat(gen_type, user_name)
                        text = "\n".join([r[3] for r in rows if r[3]])
                        msg = msg.replace("正在生成", f"正在生成{user_name}内的")
                        msg += f"共{len(text.split("\n"))}条有效发言..."
                    else:
                        rows = self.read_chat(gen_type, self.owner_id, user_id)
                        text = "\n".join([r[3] for r in rows if r[3]])
                        user_name = get_user_name(self.robot, user_id)
                        msg = msg.replace("正在生成", f"正在生成{user_name}的")
                        msg += f"共{len(text.split("\n"))}条有效发言..."
                else:
                    rows = self.read_chat(gen_type, self.owner_id, user_id)
                    text = "\n".join([r[3] for r in rows if r[3]])
                    msg += f"共{len(text.split("\n"))}条有效发言..."
                if not text:
                    msg = "没有消息记录哦~"
                    self.reply(msg, reply=True)
                    return
                self.printf(f"{self.owner_id}{f"内{user_id}的" if user_id else ""}有效发言共{len(text.split("\n"))}条")
                msg += "请耐心等待..."
                self.reply(msg, reply=True)
                set_emoji(self.robot, self.event.msg_id, 60)
                try:
                    url = self.generate_wordcloud(text)
                    msg = f"[CQ:image,file={url}]"
                except Exception:
                    self.errorf(traceback.format_exc())
                    msg = "词云生成错误！\n" + get_error()
            elif not self.config[self.owner_id]["record"]["enable"]:
                msg = "请先开启开启消息记录哦~"
            else:
                msg = "没有任何消息记录哦~"
        else:
            return
        self.success = True
        self.reply(msg, reply=True)

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"(发言|群聊|聊天|消息)(排行|统计)"), success=False)
    def statistics(self):
        """发言排行"""
        date_pattern = "历史|全部|今天|今日|本日|这天|昨天|昨日|前天|前日|本周|这周|此周|这个?礼拜|这个?星期|上周|上个?礼拜|上个?星期|本月|这月|次月|这个月|上个?月|今年|本年|此年|这一?年|去年|上一?年"
        if self.match(r"(开启|启用|打开|记录|启动|关闭|禁用|取消)"):
            if self.auth <= 1:
                self.record_switch()
                return
            else:
                msg = "你没有此操作的权限！"
        elif result := self.match(rf"(给|为)?([^\s]*?)?\s?(生成|的)?({date_pattern})?的?(发言|群聊|聊天|消息)(排行|统计)"):
            if self.config[self.owner_id]["record"]["enable"]:
                gen_type = "all"
                if self.match(r"(今天|今日|本日|这天)"):
                    gen_type = "today"
                elif self.match(r"(昨天|昨日)"):
                    gen_type = "yesterday"
                elif self.match(r"(前天|前日)"):
                    gen_type = "before_yesterday"
                elif self.match(r"(本周|这周|此周|这个?礼拜|这个?星期)"):
                    gen_type = "this_week"
                elif self.match(r"(上周|上个?礼拜|上个?星期)"):
                    gen_type = "last_week"
                elif self.match(r"(本月|这月|次月|这个月)"):
                    gen_type = "this_month"
                elif self.match(r"(上个?月)"):
                    gen_type = "last_month"
                elif self.match(r"(今年|本年|此年|这一?年)"):
                    gen_type = "this_year"
                elif self.match(r"(去年|上一?年)"):
                    gen_type = "last_year"
                cn_type = self.en2cn_dict.get(gen_type, "历史")
                msg = f"正在生成{cn_type}发言排行..."
                rows = []
                count = 0
                user_name = result.group(2)
                user_id = None
                if user_name:
                    user_id = self.get_uid(user_name)
                    if not user_id and user_name not in self.robot.data.keys():
                        self.reply(f"未检索到关于{user_name}的消息记录")
                        return
                    elif user_name in self.robot.data.keys():
                        rows = self.read_tally(gen_type, user_name)
                        count = 0
                        for row in rows:
                            count += int(row[3]) + int(row[4]) + int(row[5]) + int(row[6])
                    else:
                        rows = self.read_tally(gen_type, self.owner_id, user_id)
                        count = 0
                        for row in rows:
                            count += int(row[3]) + int(row[4]) + int(row[5]) + int(row[6])
                else:
                    rows = self.read_tally(gen_type, self.owner_id, user_id)
                    count = 0
                    for row in rows:
                        count += int(row[3]) + int(row[4]) + int(row[5]) + int(row[6])
                if len(rows) == 0:
                    msg = "没有消息记录哦~"
                    self.reply(msg, reply=True)
                    return
                self.printf(f"{self.owner_id}{f"内{user_id}的" if user_id else ""}发言共{count}条")
                set_emoji(self.robot, self.event.msg_id, 60)
                try:
                    url = self.generate_statistics(rows)
                    msg = f"[CQ:image,file={url}]"
                except Exception:
                    self.errorf(traceback.format_exc())
                    msg = "发言排行生成错误！\n" + get_error()
            elif not self.config[self.owner_id]["record"]["enable"]:
                msg = "请先开启开启消息记录哦~"
            else:
                msg = "没有任何消息记录哦~"
        else:
            return
        self.success = True
        self.reply(msg, reply=True)

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"复读(统计|记录|排行榜?)"), success=False)
    def repeat(self):
        """复读"""
        date_pattern = "历史|全部|今天|今日|本日|这天|昨天|昨日|前天|前日|本周|这周|此周|这个?礼拜|这个?星期|上周|上个?礼拜|上个?星期|本月|这月|次月|这个月|上个?月|今年|本年|此年|这一?年|去年|上一?年"
        if self.match(r"(开启|启用|打开|记录|启动)"):
            self.config[self.owner_id]["repeat_record"]["enable"] = True
            msg = "复读统计已开启"
            self.save_config()
        elif self.match(r"(关闭|禁用|取消)"):
            self.config[self.owner_id]["repeat_record"]["enable"] = False
            msg = "复读统计已关闭"
            self.save_config()
        elif match := self.match(rf"(生成)?({date_pattern})?的?复读(统计|记录|排行榜?)"):
            if self.config[self.owner_id]["repeat_record"]["enable"]:
                if self.match(r"(今天|今日)"):
                    gen_type = "today"
                elif self.match(r"(昨天|昨日)"):
                    gen_type = "yesterday"
                elif self.match(r"(前天|前日)"):
                    gen_type = "before_yesterday"
                elif self.match(r"(本周|这周|此周|这个?礼拜|这个?星期)"):
                    gen_type = "this_week"
                elif self.match(r"(上周|上个?礼拜|上个?星期)"):
                    gen_type = "last_week"
                elif self.match(r"(本月|这月|次月|这个月)"):
                    gen_type = "this_month"
                elif self.match(r"(上个?月)"):
                    gen_type = "last_month"
                elif self.match(r"(今年|本年|此年|这一?年)"):
                    gen_type = "this_year"
                elif self.match(r"(去年|上个?年)"):
                    gen_type = "last_year"
                else:
                    gen_type = "all"
                data = self.get_repeat_record(gen_type, self.owner_id)
                if not data or data == [[]]:
                    msg = "没有复读记录哦~"
                else:
                    msg = self.format_repeat_record(data, gen_type)
                    gen_type = match.group(2) or "历史"
                    self.reply_forward(self.node(msg), source=f"{gen_type}复读排行")
                    return
            else:
                msg = "请先开启复读记录哦~"
        else:
            return
        self.success = True
        self.reply(msg, reply=True)

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"^(\S+)(说|言)(道|过)?(:|：)([\S+ ]+)"))
    def once_said(self):
        """曾言道"""
        msg_said = re.findall(r"(\S+)(说|言)(道|过)?(:|：)([\S ]+)", self.event.msg)
        msg_list = []
        name_set = set()
        for said in msg_said:
            name = re.sub(r"曾?经?又?还?也?$", "", said[0])
            name_set.add(name)
            # 防止某些图片发不出来
            content = re.sub(r",sub_type=\d", "", said[-1])
            content = content.replace(r"\n", "\n").strip()
            uid = self.get_uid(name)
            if uid in self.config[self.owner_id]["users"]:
                name = self.config[self.owner_id]["users"][uid]["nickname"]
            elif name.isdigit():
                name = get_user_name(self.robot, name)
            if re.search(r"^(我|吾|俺|朕|孤)$", name):
                name = self.event.user_name
                uid = self.event.user_id
            msg_list.append(self.node(content, user_id=uid, nickname=name))
        if msg_list:
            if len(name_set) == 1:
                return self.reply_forward(msg_list, source=f"{name}的聊天记录")
            return self.reply_forward(msg_list)
        else:
            msg = "生成转发消息错误~"
            self.reply(msg)

    @via(lambda self: self.match(r"^\[CQ:record.*\]$"))
    def fix_record_file(self):
        """使用API获取语音消息正确格式的语音文件"""
        if match := self.match(r"^\[CQ:record.*,file=([^,]+).*\]$"):
            file_id = match.group(1)
            get_record(self.robot, file_id)

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"^(刚刚|刚才|先前)?\S{0,3}(说|撤回)了?(什么|啥)"))
    def what_recall(self):
        """撤回了什么"""
        if messages := self.robot.data.get("latest_recall",{}).get(self.owner_id):
            if not self.is_private():
                set_emoji(self.robot, self.event.msg_id, 124)
            nodes = []
            llm_stt = self.robot.func.get("llm_stt")
            for msg in messages:
                if msg.get("time") and time.time() - msg.get("time") > 3600:
                    continue
                user_id = msg.get("user_id")
                nickname = msg.get("sender",{}).get("nickname","")
                content = html.unescape(msg.get("message",""))
                content = re.sub(r",sub_type=\d", "", content)
                match = re.search(r"\[CQ:record.*path=([^,]+).*\]", content)
                text = "未知语音"
                if match and llm_stt:
                    try:
                        file_path = match.group(1)
                        if qq_data := self.config["qq_data"]:
                            file_path = file_path.replace("/app/.config/QQ", qq_data) + ".mp3"
                        record = open(file_path, "rb").read()
                        text = llm_stt(file = {"file": ("r.mp3", record, "audio/mpeg") })
                        b64 = base64.b64encode(record).decode()
                        nodes.append(self.node(
                            f"[CQ:file,name=语音.mp3,file=base64://{b64}]",
                            user_id=user_id, nickname=nickname
                        ))
                    except Exception:
                        self.errorf(traceback.format_exc())
                content = re.sub(r"\[CQ:record.*\]", f"[语音:{text.strip()}]", content)
                nodes.append(self.node(content, user_id=user_id, nickname=nickname))
            result = self.reply_forward(nodes, "一小时内撤回消息列表")
            if not status_ok(result):
                # 一般是发送图片出错
                for node in nodes:
                    node["data"]["content"] = re.sub(r"\[CQ:image.*\]", "[未知图片]", node["data"]["content"])
                self.reply_forward(nodes, "一小时内撤回消息列表")
        else:
            self.reply("什么也没有哦~")

    @via(lambda self: self.at_or_private() and self.au(2)
          and (self.match(r"直链\s?\[CQ:image\S*\]")
               or self.match(r"\[CQ:reply,id=([^\]]+?)\]\s?(直链)?$")), success=False)
    def sticker_url(self):
        """获取表情链接"""
        url = ""
        if match := re.search(r"\[CQ:image.*url=([^,\]]+?),.*\]", self.event.text):
            url = match.group(1)
        elif self.match(r"\[CQ:reply,id=([^\]]+?)\]"):
            msg = self.get_reply()
            if msg and re.search(r"\[CQ:image.*url=([^,\]]+?),.*\]", msg):
                url = re.search(r"\[CQ:image.*url=([^,\]]+?),.*\]", msg).group(1)
        if not url:
            return
        elif len(url) > 100:
            self.reply_forward(self.node(url), source="图片直链")
        else:
            self.reply(url, reply=True)
        self.success = True

    @via(lambda self: self.au(2) and self.at_or_private() and self.match(r"(\S+?)(又|也|同时|人)能?被?(称|叫)(为|做)?(\S+)$"))
    def set_label(self):
        """设置称号"""
        inputs = self.match(r"(\S+?)(又|也|同时)能?被?(称|叫)(为|做)?(\S+)").groups()
        name = inputs[0]
        label = inputs[-1]
        msg = "好像没有检索到这个用户欸~"
        if name.isdigit():
            info = get_stranger_info(self.robot, name)
            if status_ok(info):
                nickname = info["data"]["nickname"]
                msg = f"我记住了，{nickname}人送外号: {label}！"
                self.record_user(name, nickname, label)
        elif re.search(r"^(我|吾|俺|朕|孤)$", name):
            msg = f"我记住了，{self.event.user_name}人送外号: {label}！"
            self.record_user(
                self.event.user_id, self.event.user_name, label
            )
        else:
            for uid, user in self.config[self.owner_id]["users"].items():
                if name == uid or name == user["nickname"]:
                    self.record_user(uid, name, label)
                    msg = f"我记住了，{name}人送外号: {label}！"
                    break
        self.reply(msg)

    @via(lambda self: self.at_or_private() and self.au(2) and self.match(r"^成员列表$"))
    def show_label(self):
        """成员列表"""
        nodes = []
        for uid, user in self.config[self.owner_id]["users"].items():
            msg = f"QQ: {uid}"
            msg += f"\n昵称: {user["nickname"]}"
            label = user["label"] if user["label"] else "无"
            msg += f"\n称号: {label}"
            nodes.append(self.node(msg))
        self.reply_forward(nodes, source="成员列表")

    @via(lambda self: self.au(2) and not self.is_private() and self.match(r"^\[CQ:.*\]?[❤️\s]+$") and self.is_reply())
    def praise(self):
        """一键发电"""
        praise_times = self.event.text.count("❤")
        reply_match = self.is_reply()
        msg_id = reply_match.group(1)
        emoji_list = [2, 6, 18, 63, 66, 76, 109, 116, 144, 175, 305, 311, 318, 319, 320, 350, 337, 339, 424, 426]
        times = 1
        for emoji in emoji_list:
            if times > praise_times:
                return
            set_emoji(self.robot, msg_id, emoji)
            times += 1
            time.sleep(0.1)

    @via(lambda self: self.au(2) and not self.is_private() and self.match(r"^\[CQ:.*\](屎|史|💩)$") and self.is_reply())
    def shit_msg(self):
        """屎"""
        reply_match = self.is_reply()
        msg_id = reply_match.group(1)
        set_emoji(self.robot, msg_id, 59)

    @via(lambda self: self.event.user_id not in self.config[self.owner_id]["users"]
         or self.event.user_name != self.config[self.owner_id]["users"].get(self.event.user_id,{}).get("nickname",""), success=False)
    def a_record_user(self):
        """用户记录"""
        self.record_user(self.event.user_id, self.event.user_name)

    @via(lambda self: self.config[self.owner_id]["record"]["enable"]
         and self.event.post_type in ["message", "message_sent"], success=False)
    def a_record_msg(self):
        """聊天消息记录"""
        self.count_chat(self.owner_id, self.event.user_id, self.event.text)
        # 去CQ码
        msg = re.sub(r"(\[|【|{)[\s\S]*(\]|】|})", "", self.event.text)
        # 去URL
        msg = re.sub(r"http[s]?://\S+", "", msg)
        # 去重复
        msg = re.sub(r"(.+?)\1{2,}", r"\1", msg)
        self.store_chat(self.owner_id, self.event.user_id, msg)

    @via(lambda self: self.config[self.owner_id]["repeat_record"]["enable"]
         and str(self.data.past_message).count(f"'message': '{self.event.msg}'") > 1, success=False)
    def a_store_repeat(self):
        """复读消息记录"""
        self.store_repeat(self.owner_id, self.event.user_id, self.event.msg)

    def record_user(self, uid: str, name: str, label: str=""):
        """记录用户称号"""
        info = self.config[self.owner_id]["users"].get("uid")
        if info and info.get("label") == "":
            label = info.get("label")
        self.config[self.owner_id]["users"][uid] = {"nickname": name, "label": label}
        self.save_config()

    def get_uid(self, name):
        """使用用户名获取ID"""
        if match := re.search(r"\[CQ:at,qq=(\d+)\]", name):
            return match.group(1)
        config = self.config[self.owner_id]
        if name in config["users"]:
            return name
        if name in self.robot.user_dict:
            return name
        for uid, user_name in self.robot.user_dict.items():
            if name == user_name:
                return uid
        for uid, user in config["users"].items():
            if name in (user["nickname"], user["label"]):
                return uid
        if re.search(r"^(我|吾|俺|朕|孤)$", name):
            return self.event.user_id
        if name.isdigit():
            return name
        member_list = get_group_member_list(self.robot, self.event.group_id).get("data", [])
        for member in member_list:
            if name == member["card"] or name == member["nickname"]:
                return member["user_id"]
        return 0

    def count_chat(self, owner_id: str, user_id: str, content: str):
        """将聊天按类型记录分类计数写入数据库"""
        try:
            text = sticker = image = others = 0
            if re.search(r"^\[CQ:image.*sub_type=0.*\]$", content):
                image += 1
            elif re.search(r"^\[CQ:image.*\]$", content):
                sticker += 1
            elif re.search(r"^\[CQ:.*\]$", content):
                others += 1
            else:
                text += 1
            ts = datetime.datetime.now()
            date = ts.strftime("%Y%m%d")
            db = self.get_data_path(self.config["database"])
            conn = sqlite3.connect(db)
            self.init_db(conn, "tally")
            cur = conn.cursor()
            cur.execute(
                "SELECT text, sticker, image, others FROM tally WHERE owner_id=? AND user_id=? AND date=?",
                (owner_id, user_id, date),
            )
            row = cur.fetchone()
            if row:
                text += row[0]
                sticker += row[1]
                image += row[2]
                others += row[3]
                cur.execute(
                    "UPDATE tally SET text=?, sticker=?, image=?, others=?, update_ts=? WHERE owner_id=? AND user_id=? AND date=?",
                    (text, sticker, image, others, ts.isoformat(), owner_id, user_id, date),
                )
            else:
                cur.execute(
                    "INSERT OR REPLACE INTO tally(owner_id, user_id, date, text, sticker, image, others, update_ts) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (owner_id, user_id, date, text, sticker, image, others, ts.isoformat()),
                )
            conn.commit()
            conn.close()
        except Exception:
            self.errorf("保存消息记录失败:\n" + traceback.format_exc())

    def read_tally(self, gen_type: str, owner_id: str, user_id: str = None) -> list:
        """读取当前会话下的所有消息的计数
        gen_type 可选：today, yesterday, before_yesterday, this_week,
        last_week, this_month, last_month, this_year, last_year, all
        """
        try:
            chat_db = self.get_data_path(self.config["database"])
            date_range = self.get_date_range(gen_type)

            query = "SELECT owner_id, user_id, date, text, sticker, image, others FROM tally"
            conditions = ["owner_id=?"]
            params = [owner_id]

            if user_id:
                conditions.append("user_id=?")
                params.append(user_id)

            if date_range != (None, None):
                start_date = date_range[0].strftime("%Y%m%d")
                end_date = date_range[1].strftime("%Y%m%d")
                conditions.append("date>=?")
                conditions.append("date<=?")
                params.extend([start_date, end_date])

            where_clause = " WHERE " + " AND ".join(conditions)
            query = f"{query}{where_clause} ORDER BY date ASC"

            with sqlite3.connect(chat_db) as conn:
                self.init_db(conn, "tally")
                cur = conn.cursor()
                cur.execute(query, params)
                rows = cur.fetchall()
            if not rows:
                return []
            return rows
        except Exception:
            self.errorf(traceback.format_exc())
            return

    def store_chat(self, owner_id: str, user_id: str, text: str):
        """将单条聊天记录按 (owner_id, user_id, date) 合并写入数据库"""
        try:
            if not text:
                return
            ts = datetime.datetime.now()
            date = ts.strftime("%Y%m%d")
            db = self.get_data_path(self.config["database"])
            conn = sqlite3.connect(db)
            self.init_db(conn, "chat")
            cur = conn.cursor()
            cur.execute(
                "SELECT text FROM chat WHERE owner_id=? AND user_id=? AND date=?",
                (owner_id, user_id, date),
            )
            row = cur.fetchone()
            if row and row[0]:
                new_text = row[0] + "\n" + text
                cur.execute(
                    "UPDATE chat SET text=?, update_ts=? WHERE owner_id=? AND user_id=? AND date=?",
                    (new_text, ts.isoformat(), owner_id, user_id, date),
                )
            else:
                cur.execute(
                    "INSERT OR REPLACE INTO chat(owner_id, user_id, date, text, update_ts) VALUES (?, ?, ?, ?, ?)",
                    (owner_id, user_id, date, text, ts.isoformat()),
                )
            conn.commit()
            conn.close()
        except Exception:
            self.errorf("保存消息记录失败:\n" + traceback.format_exc())

    def read_chat(self, gen_type: str, owner_id: str, user_id: str = None) -> list:
        """读取当前会话下的所有消息并拼接为字符串返回
        gen_type 可选：today, yesterday, before_yesterday, this_week,
        last_week, this_month, last_month, this_year, last_year, all
        """
        try:
            chat_db = self.get_data_path(self.config["database"])
            date_range = self.get_date_range(gen_type)

            query = "SELECT owner_id, user_id, date, text FROM chat"
            conditions = ["owner_id=?"]
            params = [owner_id]

            if user_id:
                conditions.append("user_id=?")
                params.append(user_id)

            if date_range != (None, None):
                start_date = date_range[0].strftime("%Y%m%d")
                end_date = date_range[1].strftime("%Y%m%d")
                conditions.append("date>=?")
                conditions.append("date<=?")
                params.extend([start_date, end_date])

            where_clause = " WHERE " + " AND ".join(conditions)
            query = f"{query}{where_clause} ORDER BY date ASC"

            with sqlite3.connect(chat_db) as conn:
                self.init_db(conn, "chat")
                cur = conn.cursor()
                cur.execute(query, params)
                rows = cur.fetchall()
            if not rows:
                return []
            return rows
        except Exception:
            self.errorf(traceback.format_exc())
            return ""

    def get_date_range(self, type_name: str | None):
        """获取指定区间的日期"""
        today = datetime.date.today()
        if type_name == "all":
            return None, None
        if type_name == "today":
            s = e = today
        elif type_name == "yesterday":
            s = e = today - datetime.timedelta(days=1)
        elif type_name == "before_yesterday":
            s = e = today - datetime.timedelta(days=2)
        elif type_name == "this_week":
            start = today - datetime.timedelta(days=today.isoweekday() - 1)
            end = today
            s, e = start, end
        elif type_name == "last_week":
            this_monday = today - datetime.timedelta(days=today.isoweekday() - 1)
            start = this_monday - datetime.timedelta(days=7)
            end = start + datetime.timedelta(days=6)
            s, e = start, end
        elif type_name == "this_month":
            s = today.replace(day=1)
            e = today
        elif type_name == "last_month":
            first = today.replace(day=1)
            last_month_end = first - datetime.timedelta(days=1)
            s = last_month_end.replace(day=1)
            e = last_month_end
        elif type_name == "this_year":
            s = today.replace(month=1, day=1)
            e = today
        elif type_name == "last_year":
            s = today.replace(month=1, day=1).replace(year=today.year - 1)
            e = s.replace(month=12, day=31)
        else:
            return None, None
        return s, e

    def get_font(self) -> str:
        """获取字体路径"""
        font_path = self.get_data_path(self.config["font"])
        if not os.path.exists(font_path):
            font_path = ""
            candidates = ["SimHei", "SimSun", "Microsoft YaHei", "STHeiti",
                          "Songti", "NotoSansCJK", "PingFang"]
            for font in sorted(fm.findSystemFonts()):
                for name in candidates:
                    if name.lower() in font.lower():
                        font_path = font
                        break
                if font_path:
                    break
        return font_path

    def generate_wordcloud(self, text: str) -> str:
        """生成词云图片并返回 base64 URI(base64://...)"""

        stopwords = set()
        stopwords_path = self.get_data_path(self.config["stopwords"])
        try:
            with open(stopwords_path, "r", encoding="utf-8") as f:
                lines = [l.strip() for l in f]
        except FileNotFoundError as e:
            raise FileNotFoundError(f"未检索到可用的停词表: {e.filename}") from e
        stopwords = set(lines)
        words = jieba.lcut(text)
        filtered = []
        for w in words:
            w = w.strip()
            if not w:
                continue
            if w in stopwords:
                continue
            if re.fullmatch(r"[\s\W_]+", w):
                continue
            filtered.append(w)
        if not filtered:
            raise RuntimeError("分词后没有有效词语")

        width = height = 3000
        wc_text = " ".join(filtered)
        wc_kwargs = {
            "width": width,
            "height": height,
            "background_color": "white",
            "max_words": 300,
            "collocations": False,
            "prefer_horizontal": 0.9,
        }
        
        # 主题
        colormap = self.config[self.owner_id]["record"]["colormap"]
        if colormap:
            wc_kwargs["colormap"] = colormap

        # 字体
        font_path = self.get_font()
        if font_path:
            wc_kwargs["font_path"] = font_path
            self.printf(f"词云字体: {font_path}", False)

        # 蒙版
        img = Image.new("L", (width, height), 255)
        draw = ImageDraw.Draw(img)
        draw.rounded_rectangle((100,100,width-100,height-100), radius=500, fill=0)
        mask = np.array(img)
        wc_kwargs["mask"] = mask

        wc = WordCloud(**wc_kwargs)
        wc.generate(wc_text)
        plt.imshow(wc, interpolation="bilinear")
        plt.axis("off")
        buf = io.BytesIO()
        plt.savefig(buf, format="png", bbox_inches="tight", pad_inches=0, dpi=400)
        buf.seek(0)
        b64 = base64.b64encode(buf.read()).decode("utf-8")
        return f"base64://{b64}"

    def generate_statistics(self, data: list) -> str:
        """生成发言排行图片并返回 base64 URI(base64://...)"""

        groups = set(row[0] for row in data)
        users = set(row[1] for row in data)
        dates = set(row[2] for row in data)
        title = ""

        colormap = self.config[self.owner_id]["record"]["colormap"]
        font = fm.FontProperties(fname=self.get_font())
        fm.fontManager.addfont(self.get_font())
        font_family = [font.get_name()]
        if emoji_font_path := self.get_data_path(self.config["emoji-font"]):
            fm.fontManager.addfont(emoji_font_path)
            emoji_font = fm.FontProperties(fname=emoji_font_path)
            font_family.append(emoji_font.get_name())
        plt.rcParams["font.family"] = font_family
        plt.rcParams['font.size'] = 18
        plt.figure(figsize=(19.2, 10.8), dpi=100)
        fig, ax = plt.subplots(figsize=(19.2, 10.8), dpi=100)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.spines["bottom"].set_visible(False)
        ax.spines["left"].set_visible(True)
        ax.spines["left"].set_color("gray")
        ax.tick_params(axis="both", which="both", length=0)
        ax.set_xticks([])
        
        sorted_dates = sorted(dates, key=lambda x: datetime.datetime.strptime(str(x), "%Y%m%d"))

        # 场景1：单群多用户（一个群，多个用户）
        if len(users) > 1:
            group_id = next(iter(groups))[1:]
            group_name = get_group_name(self.robot, group_id)
            member_list = get_group_member_list(self.robot, group_id).get("data", [])
            member_dict = {}
            for member in member_list:
                name = member["card"] or member["nickname"]
                # 处理所有空白字符
                if re.match(r"^[\s\u00A0\u200B\u202F\u2060\u3000\u202A\u202B\u202E\u2066\u2067]+$", name):
                    name = member["user_id"]
                member_dict[member["user_id"]] = name
            # 统计每个用户的累计消息条数（所有日期）
            counts = {}
            for _, uid, _, text, sticker, image, others in data:
                count = text + sticker + image + others
                counts[uid] = counts.get(uid, 0) + count

            sorted_users = sorted(counts.items(), key=lambda x: x[1])[-20:]
            users_sorted = [member_dict.get(int(u), get_user_name(self.robot, u)) for u, _ in sorted_users]
            counts_sorted = [c for _, c in sorted_users]

            # 绘制水平柱状图
            colors = plt.get_cmap(colormap)(np.linspace(0, 1, len(sorted_users)))
            colors = list(colors)
            random.shuffle(colors)
            plt.barh(users_sorted, counts_sorted, color=colors)
            title = f"{group_name} 发言统计({len(dates)}天共{sum(counts.values())}条)"
            if len(counts) > 20:
                title += "(仅展示前20人)"
            for i, v in enumerate(counts_sorted):
                plt.text(v + 0.1, i, f"{v}条", ha="left", va="center")

        # 场景2：单用户多日期（一个用户，多天数据）
        elif len(dates) > 1:
            user_id = next(iter(users))
            user_name = get_user_name(self.robot, user_id)
            # 统计每个日期的消息条数
            counts_by_date = {}
            for _, uid, msg_date, text, sticker, image, others in data:
                if uid == user_id:
                    count = text + sticker + image + others
                    counts_by_date[msg_date] = counts_by_date.get(msg_date, 0) + count
            # 按日期升序排序
            values = [counts_by_date[dt] for dt in sorted_dates]
            # 转换为日期格式用于绘图
            x = [datetime.datetime.strptime(str(dt), "%Y%m%d") for dt in sorted_dates]
            # 绘制折线图（日期 vs 消息条数）
            color = random.choice(plt.get_cmap(colormap))
            plt.plot(x, values, marker="o", color=color)
            plt.ylabel("消息条数")
            title = f"用户 {user_name} 每日发言频率"
            plt.xticks(rotation=45)

        # 场景3：单用户,绘制饼图
        elif len(users) == 1:
            user_id = next(iter(users))
            user_name = get_user_name(self.robot, user_id)
            total = text = sticker = image = others = 0
            for _, uid, msg_date, text, sticker, image, others in data:
                total += text + sticker + image + others
            # 绘制饼图
            labels = ["文本", "表情包", "图片", "其他"]
            sizes = [text, sticker, image, others]
            filtered_labels = [l for s, l in zip(sizes, labels) if s > 0]
            filtered_sizes = [s for s in sizes if s > 0]
            colors = plt.get_cmap(colormap)(np.linspace(0, 1, len(filtered_labels)))
            def autopct(pct, sizes, labels):
                index = autopct.i
                autopct.i += 1
                return f"{labels[index]}{sizes[index]}条 {pct:.1f}%"
            autopct.i = 0
            plt.pie(
                filtered_sizes,
                colors=colors,
                pctdistance= 0.6,
                autopct=lambda pct: autopct(pct, filtered_sizes, filtered_labels),
                startangle=180
            )
            plt.axis("equal")
            title = f"用户 {user_name} 发言统计(共{total}条)"
        else:
            raise ValueError("不支持这种统计方式")

        fig.suptitle(title, fontsize=16, y=0.95)
        date_str = ""
        sdate = datetime.datetime.strptime(sorted_dates[0], "%Y%m%d").strftime("%Y年%m月%d日")
        edate = datetime.datetime.strptime(sorted_dates[-1], "%Y%m%d").strftime("%Y年%m月%d日")
        if len(dates) == 1:
            date_str = f"{sdate}"
        else:
            date_str = f"{sdate}至{edate}"
        fig.canvas.draw()
        renderer = fig.canvas.get_renderer()
        temp_text = ax.text(0, 0, date_str, fontsize=12)
        bbox = temp_text.get_window_extent(renderer=renderer)
        text_width = bbox.width / fig.dpi / fig.get_size_inches()[0]
        fig.text(1 - text_width - 0.01, 0.01, date_str, fontsize=12, color="gray", ha="left", va="bottom")
        temp_text.remove()

        plt.tight_layout()
        buf = io.BytesIO()
        plt.savefig(buf, format="png")
        plt.close()
        buf.seek(0)
        b64 = base64.b64encode(buf.read()).decode("utf-8")
        return f"base64://{b64}"

    def record_switch(self):
        """打开或关闭消息记录"""
        msg = ""
        if self.match(r"(开启|启用|打开|记录|启动)"):
            self.config[self.owner_id]["record"]["enable"] = True
            msg = "消息记录已开启"
        elif self.match(r"(关闭|禁用|取消)"):
            self.config[self.owner_id]["record"]["enable"] = False
            msg = "消息记录已关闭"
        self.save_config()
        self.reply(msg)

    def wordcloud_colormap(self):
        """更改配色"""
        if self.match(r"#(\S+)"):
            colormap = self.match(r"#(\S+)").group(1)
            self.config[self.owner_id]["record"]["colormap"] = colormap
            self.save_config()
            msg = "配色设置成功！"
        else:
            msg = ("请使用[#配色代码]来设置配色主题,例如：“词云主题 #Pastel2”")
            self.reply(msg)
            msg = "配色代码如下"
            for i in self.colormaps_to_img():
                msg += f"[CQ:image,file={i}]"
        self.reply(msg)

    def colormaps_to_img(self, batch_size=200, width=300, height_per_map=40, dpi=50) -> str:
        """系统内colormap生成图片并返回 base64 URI(base64://...)"""
        colormaps = plt.colormaps()
        n = len(colormaps)
        n_batches = (n + batch_size - 1) // batch_size
        base64_images = []

        for i in range(n_batches):
            batch = colormaps[i*batch_size:(i+1)*batch_size]
            height = height_per_map * len(batch)
            _, axes = plt.subplots(len(batch), 1, figsize=(width/dpi, height/dpi), dpi=dpi)

            for ax, name in zip(axes, batch):
                gradient = np.linspace(0, 1, 256).reshape(1, -1)
                ax.imshow(gradient, aspect="auto", cmap=plt.get_cmap(name))
                ax.set_axis_off()
                ax.set_title(name, fontsize=10, loc="center")

            plt.tight_layout()

            buf = io.BytesIO()
            plt.savefig(buf, format="jpg", bbox_inches="tight", pad_inches=0, dpi=dpi*4)
            buf.seek(0)
            b64 = base64.b64encode(buf.read()).decode("utf-8")
            base64_images.append(f"base64://{b64}")
            plt.close()

        return base64_images

    def init_db(self, conn: sqlite3.Connection, db_name: str):
        """确保数据库内指定表存在。
        repeat表结构: owner_id, user_id, date, text, update_ts
        chat表结构: owner_id, user_id, date, text, update_ts
        tally表结构: owner_id, user_id, date, text, sticker, image, others, update_ts
        """
        cur = conn.cursor()
        if db_name == "repeat":
            cur.execute("""
                CREATE TABLE IF NOT EXISTS repeat (                   -- 复读表
                    owner_id TEXT,                      -- 组ID
                    user_id INTEGER,                    -- 用户ID
                    date TEXT NOT NULL,                 -- YYYYMMDD
                    text TEXT,                          -- 复读内容
                    update_ts TEXT,                     -- 时间
                    PRIMARY KEY (owner_id, user_id, date)
                );""")
        elif db_name == "chat":
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS chat (                     -- 发言表
                    owner_id TEXT NOT NULL,            -- 组ID
                    user_id TEXT NOT NULL,             -- 用户ID
                    date TEXT NOT NULL,                -- YYYYMMDD
                    text TEXT,                         -- 发言内容
                    update_ts TEXT,                    -- 时间
                    PRIMARY KEY (owner_id, user_id, date)
                );""")
        elif db_name == "tally":
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS tally (                     -- 计数表
                    owner_id TEXT NOT NULL,            -- 组ID
                    user_id TEXT NOT NULL,             -- 用户ID
                    date TEXT NOT NULL,                -- YYYYMMDD
                    text INTEGER,                      -- 文本数量
                    sticker INTEGER,                   -- 表情包数量
                    image INTEGER,                     -- 表情包数量
                    others INTEGER,                    -- 时间
                    update_ts TEXT,                    -- 时间
                    PRIMARY KEY (owner_id, user_id, date)
                );""")
        conn.commit()

    def store_repeat(self, owner_id: str, user_id: str, text: str, ts = None):
        """存储复读记录"""
        try:
            if not text:
                return
            if ts is None:
                ts = datetime.datetime.now()
            date = ts.strftime("%Y%m%d")
            db_path = self.get_data_path(self.config["database"])
            conn = sqlite3.connect(db_path)
            self.init_db(conn, "repeat")
            cursor = conn.cursor()
            cursor.execute(
                "INSERT INTO repeat VALUES (?, ?, ?, ?, ?);",
                (
                    owner_id,
                    user_id,
                    date,
                    text,
                    ts.isoformat(),
                )
            )
            conn.commit()
            conn.close()
        except Exception:
            self.errorf("保存复读记录失败:\n" + traceback.format_exc())

    def get_repeat_record(self, gen_type: str, owner_id: str):
        """获取复读记录"""
        db_path = self.get_data_path(self.config["database"])
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()

        query = "SELECT * FROM repeat"
        params = [owner_id]
        conditions = ["OWNER_ID=?"]

        date_range = self.get_date_range(gen_type)
        if date_range != (None, None):
            start_date = date_range[0].strftime("%Y%m%d")
            end_date = date_range[1].strftime("%Y%m%d")
            conditions.append("date>=?")
            conditions.append("date<=?")
            params.extend([start_date, end_date])

        where_clause = " WHERE " + " AND ".join(conditions)
        query = f"{query}{where_clause} ORDER BY date ASC"

        cursor.execute(query, params)
        rows = cursor.fetchall()
        conn.close()
        return rows

    def format_repeat_record(self, data: list, gen_type: str):
        """格式化复读排行榜"""
        date_dict = {
            "today": "今日",
            "yesterday": "昨天",
            "before_yesterday": "前天",
            "this_week": "本周",
            "last_week": "上周",
            "this_month": "本月",
            "last_month": "上个月",
            "this_year": "今年",
            "last_year": "去年",
            "all": "历史",
        }
        type_text = date_dict[gen_type] if gen_type in date_dict else "历史"
        msg = "%ROBOT_NAME%复读统计开始啦~"
        total_repeat_times = len(data)
        msg += f"\n{type_text}共复读{total_repeat_times}次"
        text_count_dict = {}
        for item in data:
            if item[3] in text_count_dict:
                text_count_dict[item[3]] += 1
            else:
                text_count_dict[item[3]] = 1
        text_sorted = sorted(text_count_dict.items(), key=lambda x: x[1], reverse=True)
        msg += f"\n\n其中，被复读最多次的是“{text_sorted[0][0]}”，共被复读了{text_sorted[0][1]}次"
        user_count_dict = {}
        for item in data:
            if item[1] in user_count_dict:
                user_count_dict[item[1]] += 1
            else:
                user_count_dict[item[1]] = 1
        user_sorted = sorted(user_count_dict.items(), key=lambda x: x[1], reverse=True)
        mvp_dict = {}
        for item in data:
            if user_sorted[0][0] != item[1]:
                continue
            if item[3] in mvp_dict:
                mvp_dict[item[3]] += 1
            else:
                mvp_dict[item[3]] = 1
        mvp_dict = sorted(mvp_dict.items(), key=lambda x: x[1], reverse=True)
        if not self.event.group_id:
            return msg
        msg += f"\n\n[CQ:at,qq={user_sorted[0][0]}]复读的最勤快了，把“{mvp_dict[0][0]}”复读了{mvp_dict[0][1]}次"
        if total_repeat_times >= 20 and total_repeat_times < 50 and len(text_sorted) >= 3:
            msg += "\n\n此外，这是复读次数排行榜:"
            msg += f"\n第一名: {text_sorted[0][0]}, 计数{text_sorted[0][1]}次"
            msg += f"\n第二名: {text_sorted[1][0]}, 计数{text_sorted[1][1]}次"
            msg += f"\n第三名: {text_sorted[2][0]}, 计数{text_sorted[2][1]}次"
        elif total_repeat_times >= 50 and len(text_sorted) >= 5:
            msg += "\n\n此外，这是复读次数排行榜:"
            msg += f"\n第一名: {text_sorted[0][0]}, 计数{text_sorted[0][1]}次"
            msg += f"\n第二名: {text_sorted[1][0]}, 计数{text_sorted[1][1]}次"
            msg += f"\n第三名: {text_sorted[2][0]}, 计数{text_sorted[2][1]}次"
            msg += f"\n第四名: {text_sorted[3][0]}, 计数{text_sorted[3][1]}次"
            msg += f"\n第五名: {text_sorted[4][0]}, 计数{text_sorted[4][1]}次"
            msg += "\n\n这是成员复读排行榜:"
            msg += f"\n第一名: [CQ:at,qq={user_sorted[0][0]}], 计数{user_sorted[0][1]}次"
            msg += f"\n第二名: [CQ:at,qq={user_sorted[1][0]}], 计数{user_sorted[1][1]}次"
            msg += f"\n第三名: [CQ:at,qq={user_sorted[2][0]}], 计数{user_sorted[2][1]}次"
            msg += f"\n第四名: [CQ:at,qq={user_sorted[3][0]}], 计数{user_sorted[3][1]}次"
            msg += f"\n第五名: [CQ:at,qq={user_sorted[4][0]}], 计数{user_sorted[4][1]}次"
        return msg
