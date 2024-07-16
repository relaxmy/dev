#!/usr/bin/env python
# -*- coding: utf-8 -*-
import json
import random
import hashlib
import logging
import math
import sys

import numpy as np

from datetime import datetime, timedelta
from common.utils import safe_convert, hanzi_to_arabic
from common.jsonutil import format_json, try_parse_json
import uuid
import time
import re
from services import mysql_service, vehicle_service, oss_service, redis_service
# Create your models here.

TABLE_NAME = 'tuantuan.report'
REPORT_TYPE_BASIC = 1
REPORT_TYPE_DEVICE = 2

REPORT_TYPE_MAINTNCE = 11   # 车辆维保记录
REPORT_TYPE_INSURANCE = 12  # 车辆碰撞记录
REPORT_TYPE_OVERALL = 13  # 车辆维保和碰撞记录

PAY_STATUS_SUCCESS = 1

# 磷酸铁锂 电池衰减表格
LIP_DECAY_ARR = [100.0, 99.8, 99.4, 99.1, 98.8, 98.5, 98.3, 98.1, 97.9, 97.8, 97.6, 97.5, 97.4, 97.3, 97.2, 97.0, 97.0,
                 96.9, 96.8, 96.8, 96.7, 96.6, 96.6, 96.5, 96.5, 96.4, 96.4, 96.3, 96.3, 96.3, 96.3, 96.2, 96.1, 96.1,
                 96.1, 96.0, 96.0, 96.0, 95.9, 95.9, 95.9, 95.9, 95.9, 95.8, 95.8, 95.8, 95.8, 95.7, 95.7, 95.7, 95.7,
                 95.6, 95.6, 95.6, 95.6, 95.6, 95.5, 95.5, 95.5, 95.5, 95.5, 95.5, 95.4, 95.4, 95.4, 95.4, 95.3, 95.3,
                 95.3, 95.3, 95.3, 95.2, 95.2, 95.2, 95.2, 95.2, 95.2, 95.2, 95.1, 95.1, 95.1, 95.1, 95.1, 95.1, 95.0,
                 95.0, 95.0, 95.0, 95.0, 95.0, 95.0, 95.0, 94.9, 95.0, 94.9, 94.9, 94.9, 94.9, 94.9, 94.9, 94.9, 94.9,
                 94.8, 94.8, 94.8, 94.8, 94.8, 94.8, 94.7, 94.8, 94.8, 94.7, 94.7, 94.7, 94.7, 94.7, 94.6, 94.7, 94.6,
                 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.5, 94.6, 94.5, 94.5, 94.5, 94.5, 94.5, 94.5,
                 94.5, 94.5, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.3, 94.3, 94.4, 94.3,
                 94.3, 94.3, 94.3, 94.3, 94.3, 94.2, 94.2, 94.3, 94.2, 94.3, 94.2, 94.2, 94.3, 94.2, 94.2, 94.2, 94.2,
                 94.2, 94.2, 94.2, 94.1, 94.1, 94.2, 94.1, 94.1, 94.2, 94.1, 94.1, 94.1, 94.1, 94.1, 94.1, 94.1, 94.1,
                 94.1, 94.0, 94.0, 94.1, 94.0, 94.1, 94.0, 94.0, 94.0, 94.0, 94.0, 94.0, 94.0, 94.7, 94.5, 94.5, 94.4,
                 94.4, 94.4, 94.4, 94.4, 94.3, 94.3, 94.3, 94.3, 94.3, 94.2, 94.2, 94.2, 94.2, 94.2, 94.2, 94.2, 94.1,
                 94.1, 94.1, 94.1, 94.1, 94.0, 94.0, 94.0, 94.1, 94.0, 94.0, 94.0, 94.0, 93.9, 93.9, 93.9, 93.9, 93.9,
                 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8,
                 93.8, 93.8, 93.7, 93.8, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7,
                 93.7, 93.7, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.5, 93.6, 93.5, 93.6, 93.6,
                 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.6, 93.5, 93.5, 93.5, 93.5,
                 93.5, 93.4, 93.4, 93.4, 93.5, 93.4, 93.4, 93.5, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4,
                 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.3, 93.4, 93.4, 93.3, 93.3, 93.4, 93.4, 93.3, 93.3, 93.3, 93.3,
                 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.2, 93.3, 93.3, 93.3, 93.3, 93.3, 93.2, 93.2, 93.2,
                 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.1,
                 93.2, 93.1, 93.1, 93.2, 93.1, 93.2, 93.2, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1,
                 93.1, 93.1, 93.1, 93.0, 93.1, 93.1, 93.0, 93.0, 93.0, 93.5, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.2,
                 93.2, 93.2, 93.2, 93.2, 93.2, 93.1, 93.1, 93.3, 93.1, 93.1, 93.1, 93.1, 93.0, 93.0, 93.0, 93.0, 93.0,
                 93.0, 93.0, 93.0, 93.0, 93.0, 93.0, 92.9, 93.0, 92.9, 92.9, 93.0, 92.9, 92.9, 92.9, 92.9, 92.9, 92.8,
                 92.9, 92.9, 92.9, 92.9, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.7, 92.8,
                 92.8, 92.8, 92.7, 92.8, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7,
                 92.7, 92.7, 92.6, 92.7, 92.7, 92.6, 92.6, 92.6, 92.7, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6,
                 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5,
                 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.4, 92.4, 92.5, 92.4, 92.4, 92.4, 92.4, 92.5, 92.4,
                 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.3, 92.4, 92.3,
                 92.3, 92.3, 92.4, 92.3, 92.3, 92.4, 92.3, 92.3, 92.3, 92.3, 92.4, 92.3, 92.3, 92.3, 92.3, 92.3, 92.3,
                 92.3, 92.2, 92.3, 92.3, 92.3, 92.2, 92.3, 92.3, 92.3, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2,
                 92.2, 92.2, 92.2, 92.2, 92.1, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.1, 92.1, 92.2, 92.1, 92.2,
                 92.1, 92.1, 92.1, 92.2, 92.1, 92.6, 92.4, 92.4, 92.3, 92.4, 92.4, 92.4, 92.4, 92.3, 92.3, 92.3, 92.3,
                 92.3, 92.3, 92.2, 92.3, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.1, 92.2, 92.1, 92.1, 92.1, 92.1,
                 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.0, 92.0, 92.0, 92.0, 92.0, 92.0, 92.0, 92.0,
                 92.0, 92.0, 92.0, 91.9, 91.9, 92.0, 91.9, 92.0, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9, 91.8,
                 91.9, 91.9, 91.9, 91.9, 91.8, 91.8, 91.9, 91.8, 91.8, 91.8, 91.8, 91.8, 91.8, 91.8, 91.7, 91.8, 91.8,
                 91.8, 91.8, 91.7, 91.8, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.6,
                 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6,
                 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.5, 91.6, 91.6, 91.5, 91.5, 91.5, 91.5, 91.5,
                 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.6, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5,
                 91.4, 91.5, 91.5, 91.4, 91.4, 91.5, 91.4, 91.4, 91.4, 91.5, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4,
                 91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.3, 91.4, 91.3, 91.4, 91.3, 91.4, 91.4, 91.3, 91.3, 91.3,
                 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.2, 91.2, 91.3, 91.3, 91.3, 91.2, 91.2,
                 91.2, 91.7, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.4, 91.4, 91.3, 91.4, 91.4,
                 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.2, 91.3, 91.2, 91.3, 91.2,
                 91.3, 91.2, 91.2, 91.2, 91.2, 91.2, 91.2, 91.2, 91.1, 91.2, 91.2, 91.1, 91.2, 91.1, 91.1, 91.2, 91.1,
                 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.0, 91.0,
                 91.0, 91.1, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 90.9, 91.0, 91.0, 91.0, 91.0, 91.0, 90.9,
                 91.0, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.8, 90.9, 90.9, 90.9,
                 90.9, 90.9, 90.9, 90.8, 90.9, 90.8, 90.8, 90.8, 90.8, 90.8, 90.8, 90.8, 90.9, 90.8, 90.8, 90.8, 90.8,
                 90.8, 90.8, 90.7, 90.8, 90.8, 90.7, 90.8, 90.7, 90.7, 90.7, 90.7, 90.8, 90.7, 90.7, 90.7, 90.7, 90.7,
                 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7,
                 90.7, 90.6, 90.7, 90.6, 90.6, 90.6, 90.9, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6,
                 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.5, 90.5, 90.5, 90.5, 90.5, 90.6, 90.5, 90.5, 90.6,
                 90.5, 90.5, 90.5, 90.5, 90.5, 90.5, 90.5, 90.4, 90.4, 90.5, 90.4, 90.4, 90.4, 90.4, 90.4]
# 三元里 衰减表格
NOLIP_DECAY_ARR = [100.0, 99.8, 99.4, 99.1, 98.8, 98.5, 98.3, 98.1, 97.9, 97.8, 97.6, 97.5, 97.4, 97.3, 97.2, 97.0,
                   97.0, 96.9, 96.8, 96.8, 96.7, 96.6, 96.6, 96.5, 96.5, 96.4, 96.4, 96.3, 96.3, 96.3, 96.3, 96.2, 96.1,
                   96.1, 96.1, 96.0, 96.0, 96.0, 95.9, 95.9, 95.9, 95.9, 95.9, 95.8, 95.8, 95.8, 95.8, 95.7, 95.7, 95.7,
                   95.7, 95.6, 95.6, 95.6, 95.6, 95.6, 95.5, 95.5, 95.5, 95.5, 95.5, 95.5, 95.4, 95.4, 95.4, 95.4, 95.3,
                   95.3, 95.3, 95.3, 95.3, 95.2, 95.2, 95.2, 95.2, 95.2, 95.2, 95.2, 95.1, 95.1, 95.1, 95.1, 95.1, 95.1,
                   95.0, 95.0, 95.0, 95.0, 95.0, 95.0, 95.0, 95.0, 94.9, 95.0, 94.9, 94.9, 94.9, 94.9, 94.9, 94.9, 94.9,
                   94.9, 94.8, 94.8, 94.8, 94.8, 94.8, 94.8, 94.7, 94.8, 94.8, 94.7, 94.7, 94.7, 94.7, 94.7, 94.6, 94.7,
                   94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.6, 94.5, 94.6, 94.5, 94.5, 94.5, 94.5, 94.5,
                   94.5, 94.5, 94.5, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.4, 94.3, 94.3, 94.4,
                   94.3, 94.3, 94.3, 94.3, 94.3, 94.3, 94.2, 94.2, 94.3, 94.2, 94.3, 94.2, 94.2, 94.3, 94.2, 94.2, 94.2,
                   94.2, 94.2, 94.2, 94.2, 94.1, 94.1, 94.2, 94.1, 94.1, 94.2, 94.1, 94.1, 94.1, 94.1, 94.1, 94.1, 94.1,
                   94.1, 94.1, 94.0, 94.0, 94.1, 94.0, 94.1, 94.0, 94.0, 94.0, 94.0, 94.0, 94.0, 94.0, 94.7, 94.5, 94.5,
                   94.4, 94.4, 94.4, 94.4, 94.4, 94.3, 94.3, 94.3, 94.3, 94.3, 94.2, 94.2, 94.2, 94.2, 94.2, 94.2, 94.2,
                   94.1, 94.1, 94.1, 94.1, 94.1, 94.0, 94.0, 94.0, 94.1, 94.0, 94.0, 94.0, 94.0, 93.9, 93.9, 93.9, 93.9,
                   93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.9, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8, 93.8,
                   93.8, 93.8, 93.8, 93.7, 93.8, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7, 93.7,
                   93.7, 93.7, 93.7, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.6, 93.5, 93.6, 93.5, 93.6,
                   93.6, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.5, 93.6, 93.5, 93.5, 93.5,
                   93.5, 93.5, 93.4, 93.4, 93.4, 93.5, 93.4, 93.4, 93.5, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4,
                   93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.4, 93.3, 93.4, 93.4, 93.3, 93.3, 93.4, 93.4, 93.3, 93.3, 93.3,
                   93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3, 93.2, 93.3, 93.3, 93.3, 93.3, 93.3, 93.2, 93.2,
                   93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.2,
                   93.1, 93.2, 93.1, 93.1, 93.2, 93.1, 93.2, 93.2, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1, 93.1,
                   93.1, 93.1, 93.1, 93.1, 93.0, 93.1, 93.1, 93.0, 93.0, 93.0, 93.5, 93.3, 93.3, 93.3, 93.3, 93.3, 93.3,
                   93.2, 93.2, 93.2, 93.2, 93.2, 93.2, 93.1, 93.1, 93.3, 93.1, 93.1, 93.1, 93.1, 93.0, 93.0, 93.0, 93.0,
                   93.0, 93.0, 93.0, 93.0, 93.0, 93.0, 93.0, 92.9, 93.0, 92.9, 92.9, 93.0, 92.9, 92.9, 92.9, 92.9, 92.9,
                   92.8, 92.9, 92.9, 92.9, 92.9, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.8, 92.7,
                   92.8, 92.8, 92.8, 92.7, 92.8, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7, 92.7,
                   92.7, 92.7, 92.7, 92.6, 92.7, 92.7, 92.6, 92.6, 92.6, 92.7, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6,
                   92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.6, 92.5, 92.5, 92.5, 92.5, 92.5,
                   92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.5, 92.4, 92.4, 92.5, 92.4, 92.4, 92.4, 92.4, 92.5,
                   92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.4, 92.3, 92.4,
                   92.3, 92.3, 92.3, 92.4, 92.3, 92.3, 92.4, 92.3, 92.3, 92.3, 92.3, 92.4, 92.3, 92.3, 92.3, 92.3, 92.3,
                   92.3, 92.3, 92.2, 92.3, 92.3, 92.3, 92.2, 92.3, 92.3, 92.3, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2,
                   92.2, 92.2, 92.2, 92.2, 92.2, 92.1, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.1, 92.1, 92.2, 92.1,
                   92.2, 92.1, 92.1, 92.1, 92.2, 92.1, 92.6, 92.4, 92.4, 92.3, 92.4, 92.4, 92.4, 92.4, 92.3, 92.3, 92.3,
                   92.3, 92.3, 92.3, 92.2, 92.3, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.2, 92.1, 92.2, 92.1, 92.1, 92.1,
                   92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.1, 92.0, 92.0, 92.0, 92.0, 92.0, 92.0, 92.0,
                   92.0, 92.0, 92.0, 92.0, 91.9, 91.9, 92.0, 91.9, 92.0, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9, 91.9,
                   91.8, 91.9, 91.9, 91.9, 91.9, 91.8, 91.8, 91.9, 91.8, 91.8, 91.8, 91.8, 91.8, 91.8, 91.8, 91.7, 91.8,
                   91.8, 91.8, 91.8, 91.7, 91.8, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7,
                   91.6, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.7, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6,
                   91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.6, 91.5, 91.6, 91.6, 91.5, 91.5, 91.5, 91.5,
                   91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.6, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5,
                   91.5, 91.4, 91.5, 91.5, 91.4, 91.4, 91.5, 91.4, 91.4, 91.4, 91.5, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4,
                   91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.4, 91.3, 91.4, 91.3, 91.4, 91.3, 91.4, 91.4, 91.3, 91.3,
                   91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.2, 91.2, 91.3, 91.3, 91.3, 91.2,
                   91.2, 91.2, 91.7, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.5, 91.4, 91.4, 91.3, 91.4,
                   91.4, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.3, 91.2, 91.3, 91.2, 91.3,
                   91.2, 91.3, 91.2, 91.2, 91.2, 91.2, 91.2, 91.2, 91.2, 91.1, 91.2, 91.2, 91.1, 91.2, 91.1, 91.1, 91.2,
                   91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.1, 91.0,
                   91.0, 91.0, 91.1, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 91.0, 90.9, 91.0, 91.0, 91.0, 91.0, 91.0,
                   90.9, 91.0, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.9, 90.8, 90.9, 90.9,
                   90.9, 90.9, 90.9, 90.9, 90.8, 90.9, 90.8, 90.8, 90.8, 90.8, 90.8, 90.8, 90.8, 90.9, 90.8, 90.8, 90.8,
                   90.8, 90.8, 90.8, 90.7, 90.8, 90.8, 90.7, 90.8, 90.7, 90.7, 90.7, 90.7, 90.8, 90.7, 90.7, 90.7, 90.7,
                   90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7, 90.7,
                   90.7, 90.7, 90.6, 90.7, 90.6, 90.6, 90.6, 90.9, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6,
                   90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.6, 90.5, 90.5, 90.5, 90.5, 90.5, 90.6, 90.5, 90.5,
                   90.6, 90.5, 90.5, 90.5, 90.5, 90.5, 90.5, 90.5, 90.4, 90.4, 90.5, 90.4, 90.4, 90.4, 90.4, 90.4]

def get_price_by_uid(user_id):
    return {
        'basic_detection': 9.9,
        'device_detection': 49.9,
        'vehicle_insurance': 19.9,
        'vehicle_maintnce': 29.9,
        'vehicle_overall': 49.9,
    }

def get_vehicle_records_config(report_type):
    report_type = safe_convert(report_type, int, 0)
    config_map = {
        REPORT_TYPE_MAINTNCE: {
            'report_type': REPORT_TYPE_MAINTNCE,
            'min_price': 19.9,
            'report_name': '维保记录',
            'report_desc': '预计5-30分钟',
            'prices': [
                {'title': '性价比渠道', 'price': 19.9, 'desc': '优先查询经济实惠的渠道', 'source': 'che300'},
                {'title': '全渠道查询', 'price': 34.9, 'desc': '多个渠道全部查，覆盖广、成功率高', 'source': 'all'},
            ]
        },
        REPORT_TYPE_INSURANCE: {
            'report_type': REPORT_TYPE_INSURANCE,
            'min_price': 29.9,
            'report_name': '出险记录',
            'report_desc': '预计5-30分钟',
            'prices': [
                {'title': '性价比渠道', 'price': 29.9, 'desc': '优先查询经济实惠的渠道', 'source': 'che300'},
                {'title': '全渠道查询', 'price': 44.9, 'desc': '多个渠道全部查，覆盖广、成功率高', 'source': 'all'},
            ]
        },
        REPORT_TYPE_OVERALL: {
            'report_type': REPORT_TYPE_OVERALL,
            'min_price': 49.9,
            'report_name': '综合车况',
            'report_desc': '预计5-30分钟',
            'prices': [
                {'title': '性价比渠道', 'price': 49.9, 'desc': '优先查询经济实惠的渠道', 'source': 'che300'},
                {'title': '全渠道查询', 'price': 64.9, 'desc': '多个渠道全部查，覆盖广、成功率高', 'source': 'all'},
            ]
        },
    }
    return config_map.get(report_type, {})

def get_default_jdt_data(cache_jbt_data):
    if not cache_jbt_data:
        cache_jbt_data = {}
    return {
        "activateNum":0,
        "carBrand": "GREATWALL",
        "carModel": "",
        "carNum": "",
        "mBatteryInfo":{
            "bmsCheckDetail":[],
            "bmsCheckResult": {
                "batteryChargingTimes": '',
                "batteryTotalVoltage": cache_jbt_data.get('total_voltage', ''),
                "differentialPressure":"0V",
                "highestTemperature": cache_jbt_data.get('highest_temperature', ''),
                "highestVoltage": cache_jbt_data.get('highest_voltage', ''),
                "lowestTemperature": cache_jbt_data.get('lowest_temperature', ''),
                "lowestVoltage": cache_jbt_data.get('lowest_voltage', ''),
                "resistance":"",
                "socHealth":"100",
                "socPower":"96"
            },
            "singleTemperature": [],
            "singleVoltage": []
        }
    }

def record_valid_jbt_data(user_id, model_name, jbt_data):
    try:
        jbt_data = json.loads(jbt_data)
        redis_cli = redis_service.get_redis_client()
        cache_key = hashlib.md5(str('%s_%s' % (user_id, model_name)).encode()).hexdigest()
        cache_data = {
            'total_voltage': jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('batteryTotalVoltage', ''),
            'highest_voltage': jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestVoltage', ''),
            'lowest_voltage': jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('lowestVoltage', ''),
            'highest_temperature': jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestTemperature', ''),
            'lowest_temperature': jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('lowestTemperature', ''),
        }
        print('record_valid_jbt_data', user_id, model_name, cache_data)
        if cache_data['total_voltage'] and re.match(r'[0-9.]', cache_data['total_voltage'].replace('V', '')):
            redis_cli.set(cache_key, json.dumps(cache_data), ex=600)
    except Exception as e:
        print(e)

def get_valid_jbt_data(user_id, model_name):
    redis_cli = redis_service.get_redis_client()
    cache_key = hashlib.md5(str('%s_%s' % (user_id, model_name)).encode()).hexdigest()
    cache_data = redis_cli.get(cache_key)
    print('get_valid_jbt_data', user_id, model_name, cache_data)
    if cache_data:
        return json.loads(cache_data)
    return {}

def try_makeup_jbt_data(user_id, model_name, jbt_data):
    jbt_data = try_parse_json(jbt_data, {})
    try:
        if jbt_data and jbt_data.get('mBatteryInfo', {}).get('singleVoltage', []):
            cached_single_voltage = get_jbt_valid_single_voltage(user_id, model_name)
            makeup_single_voltage = []
            if cached_single_voltage:
                for idx, single_voltage in enumerate(jbt_data['mBatteryInfo']['singleVoltage']):
                    if idx > len(cached_single_voltage) - 1:
                        break
                    if not re.match(r'[0-9.]', single_voltage.get('value', '').replace('V', '')):
                        if re.match(r'[0-9.]', cached_single_voltage[idx].get('value', '').replace('V', '')):
                            jbt_data['mBatteryInfo']['singleVoltage'][idx]['value'] = cached_single_voltage[idx]['value']
                            makeup_single_voltage.append(cached_single_voltage[idx])
            print('try_makeup_jbt_data: ', makeup_single_voltage)
    except Exception as e:
        print('try_makeup_jbt_data_err:', e)
    return format_json(jbt_data)

def get_jbt_valid_single_voltage(user_id, model_name):
    redis_cli = redis_service.get_redis_client()
    cache_key = hashlib.md5(str('%s_%s_%s' % (user_id, model_name, 'single_voltage')).encode()).hexdigest()
    cache_data = redis_cli.get(cache_key)
    if cache_data:
        return try_parse_json(cache_data, [])
    return []

def record_jbt_valid_single_voltage(user_id, model_name, jbt_data):
    jbt_data = try_parse_json(jbt_data, {})
    single_voltage = jbt_data.get('mBatteryInfo', {}).get('singleVoltage', []) if jbt_data else []
    if not single_voltage:
        return
    redis_cli = redis_service.get_redis_client()
    cache_key = hashlib.md5(str('%s_%s_%s' % (user_id, model_name, 'single_voltage')).encode()).hexdigest()
    redis_cli.set(cache_key, format_json(single_voltage), ex=600)
    print(format_json(single_voltage))

def record_jbt_path_detect_times(user_id, jbt_path):
    redis_cli = redis_service.get_redis_client()
    cache_key = hashlib.md5(str('%s_%s' % (user_id, jbt_path)).encode()).hexdigest()
    redis_cli.incr(cache_key)
    redis_cli.expire(cache_key, 600)

def get_jbt_path_detect_times(user_id, jbt_path):
    redis_cli = redis_service.get_redis_client()
    cache_key = hashlib.md5(str('%s_%s' % (user_id, jbt_path)).encode()).hexdigest()
    return safe_convert(redis_cli.get(cache_key), int, 0) or 0

def generate_ordernumber():
    prefix = uuid.uuid1()
    ordernumber = datetime.now().strftime('%Y%m%d%H%M%S') + str(prefix.int)[:8]
    return ordernumber

def create_order(user_id, vin, report_type, vehicle_data, jbt_data=None, price=0):
    # 随机生成订单号
    ordernumber = generate_ordernumber()
    val_dict = {
        'ordernumber': ordernumber,
        'user_id': user_id,
        'vin': vin,
        'pay_status': 0,
        'result': '',
        'report_type': report_type,
        'vehicle_data': vehicle_data,
        'price': price,
    }
    if jbt_data:
        val_dict['jbt_data'] = jbt_data
    mysql_cli = mysql_service.get_mysql_client()
    insert_ret = mysql_cli.insert_data(TABLE_NAME, val_dict)
    if insert_ret:
        return val_dict
    return {}

def calc_remain_capacity_percent_curve(cycle_times, is_lip, is_rapid_decay):
    if not is_lip:
        # 高镍 = 4E-21C
        if cycle_times <= 500:
            remain_capacity_percent = 4 * 10 ** -21 * cycle_times ** 6 - 4 * 10 ** -17 * cycle_times ** 5 + 2 * 10 ** -13 * cycle_times ** 4 - 3 * 10 ** -10 * cycle_times ** 3 + 3 * 10 ** -7 * cycle_times ** 2 - 0.0002 * cycle_times + 0.9678
        else:
            remain_capacity_percent = -1 * 10 ** -12 * cycle_times ** 3 - 2 * 10 ** -9 * cycle_times ** 2 - 4 * 10 ** -5 * cycle_times + 0.9471 - cycle_times * 0.00002
    else:
        # 磷酸铁锂 残余容量比例 y--3E-12x?+ 1F-08X2-6E-05x + 0.9943R7主0.9975
        # y=-3E-12*C6*C6*C6 + 1E-08*C6*C6 - 6E-05*C6 + 0.9943
        remain_capacity_percent = -3 * 10 ** -12 * cycle_times ** 3 + 1 * 10 ** -8 * cycle_times ** 2 - 6 * 10 ** -5 * cycle_times + 0.9943

    return min(remain_capacity_percent, 0.99)

def calc_remain_capacity_percent(cycle_times, is_lip=True, is_rapid_decay=True):
    if not is_lip:
        if is_rapid_decay:
            # 急衰期 残余容量比例 =-4*10^-8*C6*C6*C6+10^-5*C6*C6-0.0012*C6+0.9906-C6*0.00002
            remain_capacity_percent = -4 * 10 ** -8 * cycle_times ** 3 + 10 ** -5 * cycle_times ** 2 - 0.0012 * cycle_times + 0.9906 - cycle_times * 0.00002
        else:
            # 慢衰期残余容量比例=-1*10^-12*O6*O6*O6-2*10^-9*O6*O6-4*10^-5*O6+0.9471-0.00002*O6
            remain_capacity_percent = -1 * 10 ** -12 * cycle_times ** 3 - 2 * 10 ** -9 * cycle_times ** 2 - 4 * 10 ** -5 * cycle_times + 0.9471 - cycle_times * 0.00002
    else:
        # 磷酸铁锂 残余容量比例 y--3E-12x?+ 1F-08X2-6E-05x + 0.9943R7主0.9975
        if is_rapid_decay:
            # 急衰期公式 = 4*10^-10*C6*C6*C6+7*10^-8*C6*C6-0.0001*C6+1.0016-C6*0.00002
            remain_capacity_percent = 4 * 10 ** -10 * cycle_times ** 3 + 7 * 10 ** -8 * cycle_times ** 2 - 0.0001 * cycle_times + 1.0016 - cycle_times * 0.00002
        else:
            # 慢衰期残余容量比例 =7*10^-16*O6*O6*O6+9*10^-19*O6*O6-4*10^-5*O6+0.9872-0.00002*O6
            remain_capacity_percent = -7 * 10 ** -16 * cycle_times ** 3 + 9 * 10 ** -19 * cycle_times ** 2 - 4 * 10 ** -5 * cycle_times + 0.9872 - cycle_times * 0.00002
    return min(remain_capacity_percent, 0.99)

def is_in_rapid_decay_period(is_lip, cycle_times):
    if is_lip:
        return cycle_times <= 150
    else:
        return cycle_times <= 100


def calculate_cycle_times(capacity, mileage_per, mileage, is_lip=True):
    print('calculate_cycle_time start:', capacity, mileage_per, mileage, is_lip)
    cycle_times = 1
    is_rapid_decay = True  # 急衰期
    # 残余容量比例 =-4*10^-8*C6*C6*C6+10^-5*C6*C6-0.0012*C6+0.9906-C6*0.00002
    remain_capacity_percent = calc_remain_capacity_percent(cycle_times, is_lip, is_rapid_decay)
    # 残余容量
    remain_capacity = capacity * remain_capacity_percent
    cur_mileage = remain_capacity * mileage_per
    total_mileage = 0  # 总行驶里程
    while total_mileage < mileage and cur_mileage > 0:
        cur_mileage = remain_capacity * mileage_per
        total_mileage += cur_mileage
        remain_capacity_percent = calc_remain_capacity_percent(cycle_times, is_lip, is_rapid_decay)
        # 残余容量
        remain_capacity = capacity * remain_capacity_percent
        cycle_times += 1
        if is_rapid_decay and not is_in_rapid_decay_period(is_lip, cycle_times):
            is_rapid_decay = False
        if remain_capacity_percent < 0.45:
            break
    remain_capacity_percent = min(remain_capacity_percent, 0.99)
    return cycle_times, remain_capacity_percent, cur_mileage

def calculate_battery_decay_curve(capacity, mileage_per, mileage, is_lip=True, min_capacity_percent=0.8):
    data = []
    data.append({'mileage': 0.0, 'remain_percent': 100,
                 'endurance': round(mileage_per * capacity, 2),
                 'capacity': round(capacity, 2), 'cur': 0})
    cycle_times = 1
    is_rapid_decay = True  # 急衰期
    # 残余容量比例 =-4*10^-8*C6*C6*C6+10^-5*C6*C6-0.0012*C6+0.9906-C6*0.00002
    remain_capacity_percent = calc_remain_capacity_percent_curve(cycle_times, is_lip, is_rapid_decay)
    # 残余容量
    remain_capacity = capacity * remain_capacity_percent
    cur_mileage = remain_capacity * mileage_per
    total_mileage = 0  # 总行驶里程

    x_maps = {0.0: 100}
    max_mileage = 0
    while remain_capacity_percent > min_capacity_percent and cycle_times <= 10000:
        cur_mileage = remain_capacity * mileage_per
        total_mileage += cur_mileage

        remain_capacity_percent = calc_remain_capacity_percent_curve(cycle_times, is_lip, is_rapid_decay)
        # 残余容量
        remain_capacity = capacity * remain_capacity_percent
        cycle_times += 1
        if is_rapid_decay and not is_in_rapid_decay_period(is_lip, cycle_times):
            is_rapid_decay = False
        x = round(total_mileage / 10000, 1)
        max_mileage = x
        y = round(remain_capacity_percent * 100, 1)
        if not x_maps.get(x):
            x_maps[x] = total_mileage
            current_endurance = round(mileage_per * remain_capacity_percent * capacity, 2)
            data.append({'mileage': x, 'remain_percent': y,
                         'endurance': current_endurance,
                         'capacity': round(remain_capacity, 2),
                         'cycle_times': cycle_times})
    print('max_mileage:', max_mileage, cycle_times)
    # 取40个点
    max_mileage = int(max_mileage / 10) * 10 if max_mileage > 40 else max_mileage
    step = max_mileage / 40
    step = max(round(step * 2) / 2, 1)
    cur_mileage = 0
    nodes = []
    while cur_mileage <= max_mileage:
        nodes.append(cur_mileage)
        cur_mileage += step
    samples = []
    idx = 0
    mark_cur = False
    for _d in data:
        if idx >= len(nodes):
            break

        if _d['mileage'] >= nodes[idx]:
            idx += 1
            if not mark_cur and _d['mileage'] * 10000 >= mileage:
                cur = 1
                mark_cur = True
            else:
                cur = 0
            _d['cur'] = cur
            samples.append(_d)
    if not mark_cur:
        _d = data[-1]
        _d['cur'] = 1
        samples.append(_d)
    return samples

def calculate_remain_cycle_times(capacity, mileage_per, is_lip=True, cycle_times=150):
    is_rapid_decay = is_in_rapid_decay_period(is_lip, cycle_times)
    remain_capacity_percent = calc_remain_capacity_percent(cycle_times, is_lip, is_rapid_decay)
    # 残余容量
    remain_capacity = capacity * remain_capacity_percent
    remain_mileage = 0  # 剩余行驶里程
    while remain_capacity > 0 and cycle_times <= 10000:
        cur_mileage = remain_capacity * mileage_per
        remain_mileage += cur_mileage
        remain_capacity_percent = calc_remain_capacity_percent(cycle_times, is_lip, is_rapid_decay)
        # 残余容量
        remain_capacity = capacity * remain_capacity_percent
        cycle_times += 1
        if is_rapid_decay and not is_in_rapid_decay_period(is_lip, cycle_times):
            is_rapid_decay = False
    return cycle_times, remain_capacity_percent, remain_mileage

def calculate_score(mileage):
    """
    初始容量 = 三电核心数据-电池容量（kWh）
    单WH行驶公里 = 三电核心数据-工信部纯电续航里程(km) / 初始容量
    """
    if mileage <= 0:
        return 100
    mileage_arr = [0, 60000, 90000, 120000, 160000, 500000]
    score_arr = [100, 90, 80, 70, 60, 10]
    for idx, v in enumerate(mileage_arr):
        if v >= mileage:
            break
    max_score = score_arr[idx-1]
    if idx > len(mileage_arr) - 1:
        return score_arr[-1]

    return max_score - int((mileage - mileage_arr[idx-1]) / (mileage_arr[idx] - mileage_arr[idx-1]) * (max_score - score_arr[idx]))

def calc_mileage_by_cycle_times(capacity, mileage_per, is_lip, cycle_times):
    is_raipd_decay = True
    cycle_time = 1
    # 残余容量比例 =-4*10^-8*C6*C6*C6+10^-5*C6*C6-0.0012*C6+0.9906-C6*0.00002
    remain_capacity_percent = calc_remain_capacity_percent(cycle_time, is_lip, is_raipd_decay)
    # 残余容量
    remain_capacity = capacity * remain_capacity_percent
    total_mileage = 0  # 总行驶里程
    max_cycle_time = cycle_times[-1]
    decay_curve = []
    if is_lip:
        remain_capacity_percent_arr = LIP_DECAY_ARR
    else:
        remain_capacity_percent_arr = NOLIP_DECAY_ARR
    while cycle_time <= max_cycle_time and cycle_time < len(remain_capacity_percent_arr):
        cur_mileage = remain_capacity * mileage_per
        total_mileage += cur_mileage
        remain_capacity_percent = calc_remain_capacity_percent(cycle_time, is_lip, is_raipd_decay)
        # 残余容量
        remain_capacity = capacity * remain_capacity_percent
        if cycle_time in cycle_times:
            decay_curve.append([int(total_mileage), round(remain_capacity_percent_arr[cycle_time] * capacity / 100, 2)])
        cycle_time += 1
        if is_raipd_decay and not is_in_rapid_decay_period(is_lip, cycle_time):
            is_raipd_decay = False
    return decay_curve

# 电池衰减周期
def calc_decay_curve(capacity, mileage_per, mileage, is_lip, samplings=None):
    if not samplings:
        # 5万公里为一段，前2、后2
        if mileage < 150000:
            samplings = [0, 50000, 100000, 150000, 200000]
        else:
            mid = math.floor(mileage / 100000) * 100000
            samplings = [mid - 100000, mid - 50000, mid, mid + 50000, mid + 100000]
    # 加入当前值
    if round(mileage / 10000, 1) not in [round(_s / 10000, 1) for _s in samplings]:
        for idx, sample in enumerate(samplings):
            if sample > mileage:
                samplings.insert(idx, mileage)
                break

    data = []
    for sample in samplings:
        _, remain_capacity_percent, _ = calculate_cycle_times(capacity, mileage_per, sample, is_lip)
        current_endurance = round(mileage_per * remain_capacity_percent * capacity, 2)
        current_capacity = round(remain_capacity_percent * capacity, 2)
        data.append({'mileage': round(sample / 10000, 1), 'endurance': current_endurance,
                     'capacity': current_capacity, 'cur': 1 if sample == mileage else 0})

    return data

def format_renewal_standards(renewal_standards):
    if renewal_standards:
        renewal_standards = hanzi_to_arabic(renewal_standards)
        print(renewal_standards)
        # 2年或5万公里（三包有效期） 衰减15%；6年或15万公里（整车包修期）衰减25%；8年或15万公里（动力蓄电池包修期）衰减38%  厂家免费换新
        matches = re.findall(r'(\d+)年.*?(\d+)公里.*?衰减.*?(\d+)%', renewal_standards)
        print(matches)
        if matches:
            ret = []
            for m in matches:
                (year, mileage, reduction) = m
                mileage = safe_convert(mileage, int, 0)
                if mileage > 10000:
                    ret.append({'mileage': '%s年或%s万公里以内' % (year, int(mileage / 10000)), 'reduction': '容量衰减 >%s%%' % reduction})
            if '营运车辆' in renewal_standards:
                ret.append({'mileage': '车辆使用性质要求', 'reduction': '非营运'})
            if '首任车主' in renewal_standards:
                ret.append({'mileage': '是否首任车主要', 'reduction': '是'})
            return False, ret
        else:
            matches = re.findall(r'(\d+)年.*?(\d+)公里.*?衰减到(\d+)%', renewal_standards)
            if matches:
                ret = []
                for m in matches:
                    (year, mileage, reduction) = m
                    mileage = safe_convert(mileage, int, 0)
                    reduction = 100 - safe_convert(reduction, int, 70)
                    if mileage > 10000:
                        ret.append({'mileage': '%s年或%s万公里以内' % (year, int(mileage / 10000)), 'reduction': '容量衰减 >%s%%' % reduction})
                if '营运车辆' in renewal_standards:
                    ret.append({'mileage': '车辆使用性质要求', 'reduction': '非营运'})
                if '首任车主' in renewal_standards:
                    ret.append({'mileage': '是否首任车主要', 'reduction': '是'})
                return False, ret

    return True, [
        {
            'mileage': '2年或5万公里以内',
            'reduction': '容量衰减 >15%',
        },
        {
            'mileage': '6年或15万公里以内',
            'reduction': '容量衰减 >25%',
        },
        {
            'mileage': '8年或5万公里以内',
            'reduction': '容量衰减 >35%',
        },
    ]

def format_renewal_standards_data(renewal_standards_data, is_first_owner=1, is_commerial_vehicle=0,
                                  driving_days=0, mileage=0, cycle_times=0, remain_capacity_percent=90):
    # {'first_owner': [], 'normal': [], 'no_comercial_usage': 0, 'is_general_standard': 0}
    """
    [
            {'title': '国标动力电池寿命条文1', 'standards': [
                {
                    'mileage': '8年或10万公里内',
                    'reduction': '容量保持 >80%',
                },
            ]},
    ]
    """
    battery_replace_data = {
        'is_general_standard': True,
        'battery_replacement_percent': 0,
        'battery_replacement_title': '国标电池寿命要求：符合',  # 厂家换电池条件：未达到
        'battery_replacement_desc': '容量保持（该阶段：>90%）',
    }
    battery_replacement_percent = 0
    battery_replacement_required = False
    renewal_standards = []
    if renewal_standards_data and not renewal_standards_data.get('is_general_standard') and renewal_standards_data.get('standards'):
        standards = []
        for _standard in renewal_standards_data.get('standards', []):
            standards.append({'mileage': _standard.get('title'), 'reduction': _standard.get('desc')})
        for _standard in renewal_standards_data.get('standards', []):
            if _standard.get('mileage') and _standard.get('mileage') > mileage:
                battery_replacement_percent = _standard.get('depreciation', 80)
                break
            if _standard.get('years') and driving_days > 0 and driving_days < _standard.get('years') * 365:
                battery_replacement_percent = _standard.get('depreciation', 80)
                break
            if _standard.get('cycle_times') and cycle_times < _standard.get('cycle_times'):
                battery_replacement_percent = _standard.get('depreciation', 80)
                break
        if not battery_replacement_percent:
            battery_replacement_percent = renewal_standards_data.get('standards', [])[0].get('depreciation', 0)
        battery_replacement_required = battery_replacement_percent > remain_capacity_percent
        if renewal_standards_data.get('is_first_owner') and not is_first_owner:
            battery_replacement_required = False
        if renewal_standards_data.get('no_comercial_usage') and is_commerial_vehicle:
            battery_replacement_required = False
        for _etra in renewal_standards_data.get('extra', []):
            standards.append({'mileage': _etra.get('title'), 'reduction': _etra.get('desc')})
        if standards:
            renewal_standards = [{'title': '厂商更换动力电池部分标准', 'standards': standards}]
            battery_replace_data['is_general_standard'] = False
    if not renewal_standards:
        battery_replace_data['is_general_standard'] = True
        renewal_standards = [
            {'title': '国标动力电池寿命条文1', 'standards': [
                {
                    'mileage': '8年或10万公里内',
                    'reduction': '容量保持 >80%',
                },
            ]},
            {'title': '国标动力电池寿命条文2', 'standards': [
                {
                    'mileage': '循环次数500次时',
                    'reduction': '容量保持 >90%',
                },
                {
                    'mileage': '循环次数1000次时',
                    'reduction': '容量保持 >80%',
                },
            ]},
        ]
        battery_replacement_percent = 90
        if cycle_times < 500:
            battery_replacement_percent = 90
        elif cycle_times < 1000:
            battery_replacement_percent = 80
        elif driving_days >= 8 * 365 or mileage >= 100000:
            battery_replacement_percent = 80

    battery_replace_data['battery_replacement_percent'] = battery_replacement_percent
    battery_replace_data['battery_replacement_desc'] = '容量保持（该阶段：>%s%%）' % battery_replacement_percent
    if battery_replace_data['is_general_standard']:
        if battery_replacement_required:
            battery_replace_data['battery_replacement_title'] = '国标电池寿命要求：不符合'
        else:
            battery_replace_data['battery_replacement_title'] = '国标电池寿命要求：符合'
    else:
        if battery_replacement_required:
            battery_replace_data['battery_replacement_title'] = '厂家换电池条件：达到'
        else:
            battery_replace_data['battery_replacement_title'] = '厂家换电池条件：未达到'
    return battery_replace_data, renewal_standards

# 计算质保剩余天数和续航里程
def calc_warranty_remain_days_and_endurance(warranty_data, driving_days, current_mileage, is_first_owner=1, is_commerial_vehicle=0):
    # warranty_data: {'first_owner': {'years': 5, 'mileage': 120000}, 'normal': {'years': 3, 'mileage': 60000}, 'no_comercial_usage': 1}
    remain_days = '-'
    remain_mileage = '-'
    remain_percent = 100
    if not warranty_data:
        warranty_data = {}
    if is_commerial_vehicle and warranty_data.get('no_comercial_usage', 0):
        return remain_days, remain_mileage, remain_percent
    warranty_dict = warranty_data.get('first_owner', {}) if is_first_owner else warranty_data.get('normal', {})
    if warranty_dict.get('years', 0) == vehicle_service.MAX_WARRANTY_YEARS or warranty_dict.get('years', 0) < 1:
        remain_days = '不限'
    else:
        year = warranty_dict.get('years', 0)
        if driving_days < year * 365:
            remain_days = year * 365 - driving_days
            remain_percent = round(remain_days / (year * 365) * 100, 2)
            remain_days = '%s年%s月' % ((remain_days // 365), (remain_days % 365 // 30)) if remain_days % 365 > 30 else '%s年' % (remain_days // 365)
        else:
            remain_days = '超保'
            remain_percent = 0

    current_mileage = safe_convert(current_mileage, float, 0.0)
    if warranty_dict.get('mileage', 0) == vehicle_service.MAX_WARRANTY_MILEAGE or warranty_dict.get('mileage', 0) < 1:
        remain_mileage = '不限'
    else:
        mileage = warranty_dict.get('mileage', 0)
        if current_mileage < mileage:
            remain_mileage = int(mileage - current_mileage)
            remain_percent = min(round(remain_mileage / mileage  * 100, 2), remain_percent)
            if remain_mileage > 10000:
                remain_mileage = '%s万' % round(remain_mileage / 10000, 1)
        else:
            remain_mileage = '超保'
            remain_percent = 0

    return remain_days, remain_mileage, remain_percent


def get_score_desc(score):
    if score >= 95:
        return '性能优秀'
    elif score >= 90:
        return '性能活跃'
    elif score >= 80:
        return '性能良好'
    elif score >= 70:
        return '性能衰减'
    elif score >= 60:
        return '性能衰退'
    return '性能衰退'

def calculate_battery_health(mileage):
    if mileage <= 10000:
        return 5, '准新'
    elif mileage <= 30000:
        return 4.5, '准新'
    elif mileage <= 60000:
        return 4, '活跃'
    elif mileage <= 100000:
        return 3.5, '活跃'
    elif mileage <= 150000:
        return 3, '损耗'
    elif mileage <= 200000:
        return 2.5, '损耗'
    elif mileage <= 300000:
        return 2, '衰减'
    elif mileage <= 400000:
        return 1.5, '衰减'
    elif mileage <= 500000:
        return 1, '衰退'
    return 0.5, '衰退'


def format_endurance_data(current_endurance, sliding_ratio, remain_capacity_percent, decrease_ratio,
                          report_type=REPORT_TYPE_DEVICE):
    while current_endurance > 20 and current_endurance * sliding_ratio < 20:
        sliding_ratio += 0.01

    min_endurance = round(current_endurance * (1 - sliding_ratio), 2)
    max_endurance = round(current_endurance * (1 + sliding_ratio), 2)
    if min_endurance % 100 > 10:
        start_endurance = int(min_endurance / 100) * 100
    else:
        start_endurance = int(min_endurance / 100) * 100 - 20
    if max_endurance % 100 > 90:
        total_endurance = int(max_endurance / 100) * 100 + 120
    else:
        total_endurance = int(max_endurance / 100) * 100 + 100
    return {
        "min_endurance": min_endurance,
        "max_endurance": max_endurance,
        "start_endurance": start_endurance if report_type != REPORT_TYPE_BASIC else 0,
        "current_endurance": current_endurance,
        "total_endurance": total_endurance,
        "endurance_remain_percent": round(remain_capacity_percent * decrease_ratio * 100, 2),
    }


def get_basic_report(ordernumber, report_data=None):
    data = {}
    data['ordernumber'] = ordernumber
    mysql_cli = mysql_service.get_mysql_client()
    if not report_data:
        report_data = mysql_cli.fetch_one(TABLE_NAME, conditions=['ordernumber=%s'], condvalues=[ordernumber])
    # if report_data and report_data['report_type'] == REPORT_TYPE_BASIC and report_data.get('result'):
    #     return json.loads(report_data['result']), report_data
    if not report_data:
        report_data = {}
    input_data = report_data.get('vehicle_data', '{}')
    input_data = json.loads(input_data)
    if not input_data:
        input_data = {}
    data['input_data'] = input_data

    mileage = int(input_data.get('mileage', 45000))
    vehicle_data = vehicle_service.search_vehicle(brand_name=input_data.get('brand_name', '') or input_data.get('brand', ''),
                                                  model_no=input_data.get('model_no', ''),
                                                  vin=input_data.get('vin', ''),
                                                  voltage=input_data.get('voltage', ''),
                                                  capacity=input_data.get('capacity', ''),
                                                  series_name=input_data.get('series_name', ''),
                                                  model_name=input_data.get('model_name', ''))
    if not vehicle_data:
        return {}, report_data
    print(vehicle_data)
    data['vehicle_data'] = vehicle_data

    endurance = safe_convert(vehicle_data.get('endurance', 0), int, 0)
    reference_price = round(safe_convert(vehicle_data.get('price', 0), float, 0.0), 2)
    if reference_price > 0:
        reference_price = '%s万' % reference_price
    elif vehicle_data.get('price'):
        reference_price = '%s万' % vehicle_data.get('price')
    else:
        reference_price = '-'

    data['vehicle_info'] = {
        'vin': report_data.get('vin', '12345678901234567'),
        'mileage': mileage,
        'vehicle_usage': input_data.get('vehicle_usage', '家用'),
        'is_commerial_vehicle': input_data.get('is_commerial_vehicle', 0),
        'brand': vehicle_data.get('brand_name', ''),
        'series': vehicle_data.get('series_name', ''),
        'year': input_data.get('purchase_date', '2020'),
        'model': vehicle_data.get('model_name', ''),
        'icon': oss_service.VEHICLE_ICON_PREFIX + vehicle_data.get('brand_name', '') + '.png',
        'reference_price': reference_price,
        "is_hybrid_engine": 0 if vehicle_data.get('energy_type', '') == '纯电动' else 1,  # 0: 纯电动 1: 混动
        'pure_endurance': endurance,
        'fuel_consumption': str(vehicle_data.get('fuel_consumption', '')) + 'L/100km' if vehicle_data.get('fuel_consumption', '') else ''
    }
    is_lip = True if '磷酸铁锂' in vehicle_data.get('battery_type', '')  else False
    capacity = safe_convert(vehicle_data.get('capacity'), float, 70)

    # 1. 计算循环次数
    mileage_per = round(endurance / capacity, 2) if capacity else 0
    cycle_times, remain_capacity_percent, cur_mileage = calculate_cycle_times(capacity, mileage_per, mileage, is_lip)
    print('cycle_times:', cycle_times, 'remain_capacity_percent:', remain_capacity_percent, 'cur_mileage:', cur_mileage)

    # 电池健康状态和剩余里程
    remain_cycle_times, _, remain_mileage = calculate_remain_cycle_times(capacity, mileage_per, is_lip, cycle_times)
    health_state, health_desc = calculate_battery_health(mileage)
    data['battery_health'] = {
        'cycle_times': cycle_times,
        'remain_cycle_times': remain_cycle_times,
        'remain_mileage': int(remain_mileage / 10000),
        'health_state': health_state,
        'health_desc': health_desc,
        'current_battery_capacity': safe_convert(capacity * remain_capacity_percent, int, 0),
        'battery_capacity_remain_percent': (100 - round(1 - remain_capacity_percent, 4) * 100),
        'battery_replacement_percent': vehicle_data.get('battery_replacement_percent', 90),
        'battery_replacement_title': '国标电池寿命要求：符合',
        'battery_replacement_desc': '标准循环寿命（容量>90%）',
    }

    driving_days = 0
    if input_data.get('purchase_date'):
        try:
            driving_days = (datetime.now() - datetime.strptime(input_data['purchase_date'], '%Y-%m-%d')).days
        except Exception:
            pass

    # 2. 计算参考续航里程
    current_endurance = round(mileage_per * remain_capacity_percent * capacity, 2)
    data['overview'] = {
        'score': calculate_score(mileage),
        'created_at': report_data.get('created_at', '2024-01-31 14:23:36'),
        'current_endurance': current_endurance,
        'total_endurance': endurance,
        'endurance_reduce_percent': round(100 * (endurance - current_endurance) / endurance, 2) if endurance else 0,
        'total_battery_capacity': capacity,
        'current_battery_capacity': safe_convert(capacity * remain_capacity_percent, int, 0),
        'battery_capacity_reduce_percent': round(1 - remain_capacity_percent, 4) * 100,
        'remain_capacity_percent': remain_capacity_percent,
        'mileage': mileage,

        'driving_days': driving_days,
        'warranty_status': '在保',
        "is_hybrid_engine": 0 if vehicle_data.get('energy_type', '') == '纯电动' else 1,  # 0: 纯电动 1: 混动
        'pure_endurance': endurance,
        'fuel_consumption': str(vehicle_data.get('fuel_consumption', '')) + 'L/100km' if vehicle_data.get('fuel_consumption',
                                                                                                     '') else ''
    }
    data['overview']['score_desc'] = get_score_desc(data['overview']['score'])
    endurance = vehicle_data.get('endurance', '')
    print('overview end')

    data['battery_info'] = {
        'manufacturer': vehicle_data.get('energy_brand', '') if vehicle_data.get('energy_brand', '') else '-',
        'battery_type': vehicle_data.get('battery_type', ''),
        'release_date': vehicle_data.get('release_date', ''),
        'battery_energy': str(vehicle_data.get('capacity', '')),
        'battery_energy_suffix': 'kWh',
        'battery_capacity': str(vehicle_data.get('energy_power', '')),
        'battery_capacity_suffix': 'Ah',
        'battery_endurance': str(endurance),
        'battery_endurance_suffix': 'km',
        'fuel_endurance': str(vehicle_data.get('fuel_endurance', '')),
        'fuel_endurance_suffix': 'km',
        'battery_consumption': str(vehicle_data.get('power_consumption_per_100', '')) + 'kWh/100km',
        'lowest_fuel_consumption': str(vehicle_data.get('lowest_fuel_consumption', '')) + 'L/100km' if vehicle_data.get(
            'lowest_fuel_consumption', '') else '',
        'fast_charge': str(vehicle_data.get('fast_charge', '')) + 'h',
        'slow_charge': str(vehicle_data.get('slow_charge', '')) + 'h',
    }
    # 购车时长
    purchase_period = '-'
    purchase_year = 0
    purchase_month = 0
    if driving_days < 365:
        purchase_period = '1年以内'
    else:
        purchase_period = '%s年%s个月' % ((driving_days // 365), (driving_days % 365 // 30)) if driving_days % 365 > 30 else '%s年' % (driving_days // 365)
        purchase_year = driving_days // 365
        purchase_month = driving_days % 365 // 30 if driving_days % 365 > 30 else 0

    data['battery_state'] = {
        'capacity_remain_percent': round(remain_capacity_percent * 100, 2),
        'is_first_owner': safe_convert(input_data.get('is_first_owner', 1), int, 1),
        'vehicle_usage': input_data.get('vehicle_usage', '') if input_data.get('vehicle_usage', '') else '非营运',
        'is_commerial_vehicle': input_data.get('is_commerial_vehicle', 0),
        'purchase_period': purchase_period,
        'purchase_year': purchase_year,
        'purchase_month': purchase_month,
        'mileage': mileage,  # 行驶里程
        'internal_resistance': 99.5,
        'temperature': 99.8,
        'voltage': 99.9,
        'self_discharge': 99.9,
    }

    # 耗电量
    vehicle_data = data.get('vehicle_data', {})
    power_consumption_per_100 = safe_convert(vehicle_data.get('power_consumption_per_100', ''), float, 0.0)
    if power_consumption_per_100 < 0.1:
        power_consumption_per_100 = data.get('overview', {}).get('current_battery_capacity', 0.1) * 100 / data.get('overview', {}).get('current_endurance', 1)
    power_consumption_per_100 = round(power_consumption_per_100, 2)
    fuel_consumption = safe_convert(vehicle_data.get('fuel_consumption', 0), float, 0.0)
    fuel_tank_capacity = safe_convert(vehicle_data.get('fuel_tank_capacity', ''), float, 53)
    lowest_fuel_consumption = safe_convert(vehicle_data.get('lowest_fuel_consumption', 0), float, 0.0)
    data['battery_consumption'] = {
        'stat_percentage': '80%',
        'min_battery_consumption': round(power_consumption_per_100 * 0.9, 2),
        'max_battery_consumption': round(power_consumption_per_100 * 1.1, 2),
        'min_fuel_consumption': round(lowest_fuel_consumption * 0.9, 2) if lowest_fuel_consumption else round(fuel_consumption * 0.9, 2),
        'max_fuel_consumption': round(lowest_fuel_consumption * 1.1, 2) if lowest_fuel_consumption else round(fuel_consumption * 1.1, 2),
    }

    # 3. 夏季、冬季续航
    summer_decrease_ratio = 0.83 if mileage >= 30000 else 0.9
    winter_decrease_ratio = 0.64 if mileage >= 30000 else 0.80
    low_temperature_decrease_ratio = 0.51 if mileage >= 30000 else 0.72
    summer_endurance = round(current_endurance * summer_decrease_ratio, 2)
    winter_endurance = round(current_endurance * winter_decrease_ratio, 2)
    low_temperature_endurance = round(current_endurance * low_temperature_decrease_ratio, 2)
    # 满油满电续航
    fuel_endurance = vehicle_data.get('fuel_endurance', 0)
    if fuel_endurance and fuel_endurance > endurance:
        fuel_endurance -= endurance
    else:
        fuel_endurance = int(100 * fuel_tank_capacity / (fuel_consumption * (safe_convert(endurance, int, 0) + 25) / 25)) if fuel_consumption else 330
    print('summer_endurance:', summer_endurance, 'winter_endurance:', winter_endurance, 'low_temperature_endurance:', low_temperature_endurance)
    if vehicle_data.get('energy_type', '') == '纯电动':
        data['endurance'] = {
            'summer': {
                'actual_endurance': endurance,
                "endurance": [
                    {"25℃~35℃": format_endurance_data(summer_endurance, 0.03, remain_capacity_percent, summer_decrease_ratio, report_data.get('report_type'))},
                    {"35℃~45℃": format_endurance_data(summer_endurance * 0.85, 0.05, remain_capacity_percent, summer_decrease_ratio * 0.85, report_data.get('report_type'))}
                ],
                'fast_charge': str(vehicle_data.get('fast_charge', '')) + 'h',
                'slow_charge': str(vehicle_data.get('slow_charge', '')) + 'h',
            },
            'winter': {
                'actual_endurance': endurance,
                "endurance": [
                    {"-20℃~-10℃": format_endurance_data(low_temperature_endurance, 0.07, remain_capacity_percent, low_temperature_decrease_ratio, report_data.get('report_type'))},
                    {"-10℃~0℃": format_endurance_data(winter_endurance, 0.03, remain_capacity_percent, winter_decrease_ratio, report_data.get('report_type'))},
                ],
                'fast_charge': str(vehicle_data.get('fast_charge', '')) + 'h',
                'slow_charge': str(vehicle_data.get('slow_charge', '')) + 'h',
            }
        }
    else:
        data['endurance'] = {
            'summer': {
                'actual_endurance': endurance,
                "endurance": [
                    {"纯电续航": format_endurance_data(summer_endurance, 0.03, remain_capacity_percent, summer_decrease_ratio, report_data.get('report_type'))},
                    {"满油满电续航": format_endurance_data(summer_endurance + fuel_endurance, 0.03, remain_capacity_percent, summer_decrease_ratio, report_data.get('report_type'))},
                ],
                'fast_charge': str(vehicle_data.get('fast_charge', '')) + 'h',
                'slow_charge': str(vehicle_data.get('slow_charge', '')) + 'h',
            },
            'winter': {
                'actual_endurance': endurance,
                "endurance": [
                    {"纯电续航": format_endurance_data(winter_endurance, 0.03, remain_capacity_percent, winter_decrease_ratio, report_data.get('report_type'))},
                    {"满油满电续航": format_endurance_data(winter_endurance + fuel_endurance, 0.03, remain_capacity_percent, winter_decrease_ratio, report_data.get('report_type'))},
                ],
                'fast_charge': str(vehicle_data.get('fast_charge', '')) + 'h',
                'slow_charge': str(vehicle_data.get('slow_charge', '')) + 'h',
            }
        }
    _cycle_times = [150, 1000] if is_lip else [100, 1000]
    ((fast_mileage, fast_capacity), (slow_mileage, slow_capacity)) = calc_mileage_by_cycle_times(capacity, mileage_per,
                                                                                                 is_lip, _cycle_times)
    # 检测版报告取值
    if report_data.get('report_type') == REPORT_TYPE_BASIC:
        mileage_capacity_curve = calc_decay_curve(capacity, mileage_per, mileage, is_lip,
                                                  samplings=[0, fast_mileage, slow_mileage])
    else:
        mileage_capacity_curve = calc_decay_curve(capacity, mileage_per, mileage, is_lip)
    print('mileage_capacity_curve:', mileage_capacity_curve)

    fast_remain_percent = round(fast_capacity / capacity, 2) if capacity else 0
    slow_remain_percent = round(slow_capacity / capacity, 2) if capacity else 0
    battery_decay_curve = calculate_battery_decay_curve(capacity, mileage_per, mileage, is_lip,
                                                        min(remain_capacity_percent, 0.8))
    print('calculate_battery_decay_curve:', battery_decay_curve)
    data['capacity'] = {
        'current_period': '在当前里程电池状态处于急衰期' if is_in_rapid_decay_period(is_lip, cycle_times) else '在当前里程电池状态处于慢衰期',
        'mileage_capacity_curve': mileage_capacity_curve,
        'battery_decay_curve': battery_decay_curve,
        'fast_charge_capacity': {
            'min_mileage': '0km',
            'max_mileage': '%skm' % int(fast_mileage),
            'min_capacity': '%skWh/100%s' % (capacity, '%'),
            'max_capacity': '%skWh/%s%s' % (fast_capacity, fast_remain_percent * 100, '%'),
            'min_endurance': '%skm' % endurance,
            'max_endurance': '%skm' % round(safe_convert(endurance, float, 0.0) * fast_remain_percent, 2),
            'suggestion': '建议您在急衰期内，尽量避免使用快充，以免影响电池寿命。',
        },

        'slow_charge_capacity': {
            'min_mileage': '%skm' % int(fast_mileage),
            'max_mileage': '%skm' % int(slow_mileage),
            'min_capacity': '%skWh/%s%s' % (fast_capacity, fast_remain_percent * 100, '%'),
            'max_capacity': '%skWh/%s%s' % (slow_capacity, slow_remain_percent * 100, '%'),
            'min_endurance': '%skm' % round(safe_convert(endurance, float, 0.0) * fast_remain_percent, 2),
            'max_endurance': '%skm' % round(safe_convert(endurance, float, 0.0) * slow_remain_percent, 2),
            'suggestion': '建议您在急衰期内，尽量避免使用快充，以免影响电池寿命。',
        },
    }

    is_first_owner = safe_convert(input_data.get('is_first_owner', 1), int, 1)
    is_commerial_vehicle = safe_convert(input_data.get('is_commerial_vehicle', 0), int, 0)
    p_remain_days, p_remain_mileage, p_remain_percent = calc_warranty_remain_days_and_endurance(vehicle_data.get('warranty_data', ''),
                                                                              driving_days, mileage,
                                                                              is_first_owner, is_commerial_vehicle)

    battery_replace_data, general_renewal_standards = format_renewal_standards_data(vehicle_data.get('renewal_standards_data'),
                                                                                   is_first_owner, is_commerial_vehicle,
                                                                                   driving_days, mileage, cycle_times,
                                                                                   remain_capacity_percent * 100)
    data['warranty'] = {
        'cycle_times': cycle_times,
        'warranty': vehicle_data.get('warranty', ''),
        'warranty_type': vehicle_data.get('warranty_type', ''),
        'battery_pack': {
            'remain_time': p_remain_days,
            'remain_mileage': p_remain_mileage if p_remain_mileage in ['不限', '-', '超保'] else '%skm' % p_remain_mileage,
            'remain_percent': int(p_remain_percent),
        },
        'battery_cell': {
            'remain_time': p_remain_days,
            'remain_mileage': p_remain_mileage if p_remain_mileage in ['不限', '-', '超保'] else '%skm' % p_remain_mileage,
            'remain_percent': int(p_remain_percent),
        },
        'is_general_standard': battery_replace_data.get('is_general_standard'),
        'renewal_standards': [],
        'general_renewal_standards': general_renewal_standards,
    }
    if int(p_remain_percent) == 0:
        data['overview']['warranty_status'] = '超保'
    # 更换电池条件
    data['battery_health']['battery_replacement_percent'] = battery_replace_data.get('battery_replacement_percent', 0)
    data['battery_health']['battery_replacement_title'] = battery_replace_data.get('battery_replacement_title', '')
    data['battery_health']['battery_replacement_desc'] = battery_replace_data.get('battery_replacement_desc', '')
    if report_data['report_type'] == REPORT_TYPE_BASIC:
        mysql_cli.update_data(TABLE_NAME, {'score': data['overview']['score'], 'result': format_json(data)},
                              conditions=['ordernumber=%s'], condvalues=[ordernumber])
    return data, report_data


def measure_battery_voltage(voltage_diff, is_rapid_decay):
    if is_rapid_decay:
        voltage_diff_arr = [0.02, 0.03, 0.06, 0.09, 0.12, 0.15, 0.18, 0.21, 0.24, 0.27, 0.3, sys.float_info.max]
        voltage_diff_desc = [
            ('正常', '', '', 0),
            ('正常', '', '', 0.1),
            ('正常', '', '', 0.2),
            ('一级故障', '一致性差异-低', '电池早期的一致性波动，为常见现象', 0.5),
            ('一级故障', '一致性差异-中', '电池一致性波动加大，建议尽量使用慢充', 1),
            ('一级故障', '一致性差异-高', '建议使用慢充，充满后再充4-6小时，一般通过充电均衡可恢复', 1.5),
            ('二级故障', '性能衰减-低', '电池内阻增加，续航衰减，尽量避免馈电行驶和长期闲置', 1),
            ('二级故障', '性能衰减-中', '内阻异常，建议对电池包全面检测', 1.5),
            ('二级故障', '性能衰减-高', '压差异常，建议对电池包全面检测', 2),
            ('三级故障', '电芯异常', '压差异常，疑似电芯故障，建议检修', 1.5),
            ('三级故障', '电池模组故障', '压差异常，疑似电芯故障，建议检修', 2),
            ('三级故障', '电池包故障', '压差异常，疑似电池包故障', 2.5),
        ]
    else:
        voltage_diff_arr = [0.02, 0.03, 0.06, 0.09, 0.12, 0.15, 0.18, 0.21, 0.24, 0.27, 0.3, sys.float_info.max]
        voltage_diff_desc = [
            ('正常', '', '', 0),
            ('正常', '', '', 0.2),
            ('一级故障', '一致性差异-低', '电池早期的一致性波动，为常见现象', 1),
            ('一级故障', '一致性差异-中', '电池一致性波动加大，建议尽量使用慢充', 1.5),
            ('一级故障', '一致性差异-高', '建议使用慢充，充满后再充4-6小时，一般通过充电均衡可恢复', 2),
            ('二级故障', '性能衰减-低', '电池内阻增加，续航小幅衰减，尽量避免馈电行驶和长期闲置', 1.5),
            ('二级故障', '性能衰减-中', '电池内阻增加，续航衰减，避免馈电行驶和长期闲置', 2),
            ('二级故障', '性能衰减-较高', '内阻异常，建议对电池包全面检测', 2.5),
            ('二级故障', '性能衰减-高', '压差异常，建议对电池包全面检测', 3),
            ('三级故障', '电芯异常', '压差异常，疑似电芯故障，建议检修', 2),
            ('三级故障', '电池模组故障', '压差异常，疑似电芯故障，建议检修', 2.5),
            ('三级故障', '电池包故障', '压差异常，疑似电池包故障', 3),
        ]
    voltage_diff = abs(voltage_diff)
    # voltage_diff = voltage_diff if voltage_diff < 1.5 else abs(voltage_diff - 1.5)
    for idx, v in enumerate(voltage_diff_arr):
        if voltage_diff < v:
            break
    return voltage_diff_desc[idx]

def get_battery_score_by_mileage(mileage):
    if mileage < 5000:
        return 99.9
    elif mileage < 10000:
        return 99.5
    return 99.5 - round(mileage / 30000, 2)

def detect_battery_voltage(jbt_data, is_rapid_decay, mileage):
    # 电压数据
    single_voltage_list = []
    voltage_detection_score = get_battery_score_by_mileage(mileage)
    unnormal_voltage_list = []
    max_battery_score = round(voltage_detection_score * 0.95, 2)

    single_voltage = jbt_data.get('mBatteryInfo', {}).get('singleVoltage', [])
    single_voltage_values = []
    for v in single_voltage:
        if re.match(r'[0-9.]', v.get('value', '').replace('V', '')):
            _voltage = safe_convert(v.get('value', '').replace('V', ''), float, 0.0)
            if _voltage >= 2.5 and _voltage <= 4.5:
                single_voltage_values.append(_voltage)
    # 给定的数据集
    _data = np.array(single_voltage_values)
    # 计算均值和标准差
    mean = np.mean(_data)
    std_dev = np.std(_data)
    # 计算Z得分
    z_scores = (_data - mean) / std_dev
    print('mean:', mean, 'std_dev:', std_dev, 'z_scores:', z_scores)

    unnormal_count = 0
    z_scores_idx = 0
    uniq_names = {}
    for v in single_voltage:
        if v.get('systemName'):
            if uniq_names.get(v.get('systemName')):
                continue
            uniq_names[v.get('systemName')] = 1

        _voltage = safe_convert(v.get('value', '').replace('V', ''), float, 0.0)
        if re.match(r'[0-9.]', v.get('value', '').replace('V', '')):
            # voltage_diff = z_scores[z_scores_idx] if z_scores_idx < len(z_scores) and not np.isnan(z_scores[z_scores_idx]) else 0
            voltage_diff = _voltage - mean if not np.isnan(mean) else 0
            _voltage_detection, _category, _voltage_desc, _score = measure_battery_voltage(voltage_diff, is_rapid_decay)
            z_scores_idx += 1
        else:
            continue
            # v['value'] = '-'
            # _voltage_detection, _category, _voltage_desc, _score = '不支持', '', '', 0

        v['detection'] = _voltage_detection
        v['category'] = _category
        v['desc'] = _voltage_desc
        v['voltage'] = _voltage
        if v['detection'] == '一级故障':
            v['level'] = 1
        elif v['detection'] == '二级故障':
            v['level'] = 2
        elif v['detection'] == '三级故障':
            v['level'] = 3
        else:
            v['level'] = 0
        single_voltage_list.append(v)
        if v['level'] > 0:
            unnormal_voltage_list.append(v)
            unnormal_count += 1
            unnormal_ratio = int(unnormal_count / 3) * 0.1 + 1
            voltage_detection_score -= _score * unnormal_ratio
        elif _score > 0:
            voltage_detection_score -= _score
        if v['detection'] == '二级故障':
            max_battery_score = min(max_battery_score, 80.0)
        elif v['detection'] == '三级故障':
            max_battery_score = min(max_battery_score, 60.0)
    voltage_detection_score = round(max(voltage_detection_score, 30.0), 2)
    return single_voltage_list, voltage_detection_score, unnormal_voltage_list, max_battery_score

def format_jbt_detect_data(voltage_data, suffix):
    if not voltage_data:
        return '-'
    if isinstance(voltage_data, str):
        if re.match(r'[0-9.]', voltage_data.lower().replace(suffix.lower(), '')):
            return voltage_data
    return '-'


def get_device_report(ordernumber, report_data=None, recalculate=0):
    mysql_cli = mysql_service.get_mysql_client()
    if not report_data:
        report_data = mysql_cli.fetch_one(TABLE_NAME, conditions=['ordernumber=%s'], condvalues=[ordernumber])
    if report_data and report_data.get('result') and not recalculate:
        return json.loads(report_data['result'])

    data, report_data = get_basic_report(ordernumber, report_data)

    jbt_data = {}
    try:
        jbt_data = json.loads(report_data.get('jbt_data', '{}'))
    except Exception:
        pass
    is_rapid_decay = True if data.get('battery_health', {}).get('cycle_times', 0) < 150 else False  # 急衰期

    # 公里系数
    mileage = data.get('vehicle_info', {}).get('mileage', 0)
    # 温度数据
    single_temperature_list = []
    temperature_detectioin_score = get_battery_score_by_mileage(mileage)
    unnormal_temperature_list = []
    # 电芯性能分

    try:
        single_voltage_list, voltage_detection_score, unnormal_voltage_list, max_battery_score = detect_battery_voltage(jbt_data, is_rapid_decay, mileage)

        single_temperature = jbt_data.get('mBatteryInfo', {}).get('singleTemperature', [])
        single_temperature_values = [safe_convert(v.get('value', '').replace('℃', ''), float, 0.0) for v in single_temperature if re.match(r'[0-9.]', v.get('value', '').replace('℃', ''))]
        # 给定的数据集
        _data = np.array(single_temperature_values)
        # 计算均值和标准差
        mean = np.mean(_data)
        std_dev = np.std(_data)
        # 计算Z得分
        z_scores = (_data - mean) / std_dev

        if not single_temperature:
            if jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestTemperature', 0):
                temperature_detectioin_score -= random.randint(1, 3)
            else:
                temperature_detectioin_score -= random.randint(4, 6)
        z_score_idx = 0
        for v in single_temperature:
            if re.match(r'[0-9.]', v.get('value', '').replace('℃', '')):
                # temperature_diff = z_scores[z_score_idx] if z_score_idx < len(z_scores) and not np.isnan(z_scores[z_score_idx]) else 0
                temperature_diff = safe_convert(v.get('value', '').replace('℃', ''), float, mean) - mean if not np.isnan(z_scores[z_score_idx]) else 0
                z_score_idx += 1
                if temperature_diff <= 1.5:
                    v['detection'] = '正常'
                    v['category'] = ''
                    v['desc'] = ''
                    v['level'] = 0
                else:
                    v['detection'] = '一致性差异'
                    v['level'] = 1
                    if temperature_diff <= 1.75:
                        v['category'] = '低'
                        v['desc'] = '由于排列位置不同各电芯温度差异属于常见现象，可持续观察'
                        temperature_detectioin_score -= 1
                    elif temperature_diff <= 2:
                        v['category'] = '中'
                        v['desc'] = '温差异常，建议对电池包温控和散热系统进行检查'
                        temperature_detectioin_score -= 2
                    else:
                        v['category'] = '高'
                        v['desc'] = '温差异常较大，建议对电池包温控和散热系统进行检修'
                        temperature_detectioin_score -= 3
                    unnormal_temperature_list.append(v)
            else:
                v['value'] = '-'
                v['detection'] = '不支持'
                v['category'] = ''
                v['desc'] = ''
                v['level'] = 0
            single_temperature_list.append(v)
    except Exception as e:
        print(e)
        pass
    # 电压
    normal_voltage_rate = round(100 * (len(single_voltage_list) - len(unnormal_voltage_list)) / len(single_voltage_list), 2) if single_voltage_list else 100
    total_voltage = 0.0
    for _v in single_voltage_list:
        total_voltage += _v.get('voltage', 0.0)
    # 优先用电压列表的总电压
    if total_voltage > 100:
        total_voltage = '%sV' % round(total_voltage, 3) if total_voltage > 1 else '-'
    elif jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('batteryTotalVoltage', 0) and re.match(r'[0-9.]', jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('batteryTotalVoltage', 0)):
        total_voltage = format_jbt_detect_data(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('batteryTotalVoltage', 0), 'V')
    else:
        total_voltage = '%sV' % round(total_voltage, 3) if total_voltage > 1 else '-'

    if single_voltage_list:
        highest_voltage = 0
        lowest_voltage = 99
        for _v in single_voltage_list:
            if _v.get('voltage', 0) > highest_voltage:
                highest_voltage = _v.get('voltage', 0)
            if _v.get('voltage', 0) < lowest_voltage and _v.get('voltage', 0) > 0:
                lowest_voltage = _v.get('voltage', 0)
        highest_voltage = '%sV' % round(highest_voltage, 3) if highest_voltage > 0 else '-'
        lowest_voltage = '%sV' % round(lowest_voltage, 3) if lowest_voltage < 99 else '-'
    else:
        highest_voltage = format_jbt_detect_data(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestVoltage', 0), 'V')
        lowest_voltage = format_jbt_detect_data(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('lowestVoltage', 0), 'V')

    data['battery_voltage'] = {
        'total_voltage': total_voltage,
        'highest_voltage': highest_voltage,
        'lowest_voltage': lowest_voltage,
        'single_voltage_list': single_voltage_list,
        'unnormal_voltage_list': unnormal_voltage_list,
        'detection_score': voltage_detection_score,
        'total_battery_voltage': len(single_voltage_list),
        'normal_battery_voltage': len(single_voltage_list) - len(unnormal_voltage_list),
        'normal_voltage_rate': normal_voltage_rate,
    }
    # 温度
    normal_temperature_rate = round(
        100 * (len(single_temperature_list) - len(unnormal_temperature_list)) / len(single_temperature_list),
        2) if single_temperature_list else 100
    data['battery_temperature'] = {
        'highest_temperature': format_jbt_detect_data(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestTemperature', 0), '℃'),
        'lowest_temperature': format_jbt_detect_data(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('lowestTemperature', 0), '℃'),
        'total_battery_temperature': len(single_temperature_list),
        'normal_battery_temperature': len(single_temperature_list) - len(unnormal_temperature_list),
        'normal_temperature_rate': normal_temperature_rate,
        'single_temperature_list': single_temperature_list,
        'unnormal_temperature_list': unnormal_temperature_list,
    }

    # 自放电
    self_discharge = safe_convert(jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('socHealth', 0), float, 0.0)
    if self_discharge < 30:
        self_discharge = round(voltage_detection_score * 0.9, 2)

    capacity_score = data.get('battery_state', {}).get('capacity_remain_percent', 60.0)
    # 内阻
    internal_resistance = capacity_score * 0.3 + voltage_detection_score * 0.7

    # 电芯性能分，综合分数
    battery_score = capacity_score * 0.3 + voltage_detection_score * 0.5 + temperature_detectioin_score * 0.1 + self_discharge * 0.1
    battery_score = round(battery_score, 2)
    if battery_score >= 90:
        healthy_status = '优秀'
    elif battery_score >= 80:
        healthy_status = '良好'
    elif battery_score >= 70:
        healthy_status = '一般'
    elif battery_score >= 60:
        healthy_status = '较差'
    else:
        healthy_status = '极差'

    data['overview'] = {
        'score': battery_score,
        'healthy_status': healthy_status,
        'capacity': capacity_score,
        'temperature': temperature_detectioin_score,
        'internal_resistance': internal_resistance,
        'voltage': voltage_detection_score,
        'self_discharge': self_discharge,
        'created_at': report_data.get('created_at', ''),
    }

    data.pop('jbt_data', None)
    mysql_cli.update_data(TABLE_NAME, {'score': data['overview']['score'], 'result': format_json(data)},
                          conditions=['ordernumber=%s'], condvalues=[ordernumber])
    return data

def get_report_list_by_uid(user_id, report_type, created_month, page, size, min_id, max_id):
    mysql_cli = mysql_service.get_mysql_client()
    limit = '%s, %s' % (page * size, size)
    conditions = ['user_id=%s', 'pay_status=%s']
    condvalues = [user_id, PAY_STATUS_SUCCESS]

    if report_type == 3:
        conditions.append('report_type IN (%s, %s)')
        condvalues.extend([1, 2])
    elif report_type:
        conditions.append('report_type=%s')
        condvalues.append(report_type)

    start_time = None
    end_time = None
    if created_month:
        try:
            start_time = datetime.strptime(created_month, '%Y-%m')
            end_time = (start_time + timedelta(days=32)).replace(day=1)
        except:
            pass
    orderby = 'created_at desc'
    if start_time and end_time:
        conditions.append('created_at>=%s')
        condvalues.append(start_time)
        conditions.append('created_at<%s')
        condvalues.append(end_time)
    if min_id > 0:
        conditions.append('id>%s')
        condvalues.append(min_id)
        orderby = 'created_at asc'
    elif max_id > 0:
        conditions.append('id<%s')
        condvalues.append(max_id)
        orderby = 'created_at desc'

    report_list = mysql_cli.fetch(TABLE_NAME, conditions=conditions, condvalues=condvalues,
                                  orderby=orderby, limit=limit,
                                  fields='id,ordernumber,vin,user_id,report_type,created_at,vehicle_data,score')
    if not report_list:
        return []
    # 按时间倒序
    report_list = sorted(report_list, key=lambda x: x['created_at'], reverse=True)
    for report in report_list:
        input_data = report.get('vehicle_data', '{}')
        input_data = json.loads(input_data)
        if not input_data:
            input_data = {}
        report['created_at'] = report.get('created_at', '').strftime('%Y-%m-%d %H:%M:%S')

        report.pop('jbt_data', None)
        report.pop('result', None)
        input_data = report.get('vehicle_data', '{}')
        try:
            input_data = json.loads(input_data)
        except Exception:
            input_data = {}
        report.update({
            'brand': input_data.get('brand_name', ''),
            'series': input_data.get('series_name', ''),
            'model': input_data.get('model_name', ''),
            'icon': oss_service.VEHICLE_ICON_PREFIX + input_data.get('brand_name', '') + '_' + input_data.get(
                'series_name', '') + '.png' if input_data.get('brand_name', '') and input_data.get('series_name', '') else '',
        })
        #需要参数3，然后通过参数3将1与2进行合并
    return report_list

# 校验金奔腾数据
def is_valid_jbt_data(jbt_data, valid_total_voltage=75, jbt_path='', jbt_vehicle_data=None):
    try:
        if not jbt_vehicle_data:
            jbt_vehicle_data = {}
        logger = logging.getLogger('django.server')
        logger.info('is_valid_jbt_data:%s,%s,%s' % (jbt_data, valid_total_voltage,jbt_path))
        jbt_data = json.loads(jbt_data)
        if not jbt_data:
            return False
        battery_total_voltage = jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('batteryTotalVoltage', 0)
        battery_total_voltage = safe_convert(battery_total_voltage.upper().replace('V', ''), float, 0.0) if battery_total_voltage else 0.0
        highest_voltage = jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('highestVoltage', 0)
        highest_voltage = safe_convert(highest_voltage.upper().replace('V', ''), float, 0.0) if highest_voltage else 5
        lowest_voltage = jbt_data.get('mBatteryInfo', {}).get('bmsCheckResult', {}).get('lowestVoltage', 0)
        lowest_voltage = safe_convert(lowest_voltage.upper().replace('V', ''), float, 0.0) if lowest_voltage else 0.0
        print('is_valid_jbt_data:', highest_voltage, lowest_voltage)
        voltage_list = jbt_data.get('mBatteryInfo', {}).get('singleVoltage', [])
        # 是否支持单体电压
        if not voltage_list:
            return False
        # if not voltage_list:
            # if not jbt_vehicle_data.get('support_voltage_list', True):
            #     return True if battery_total_voltage > 0 else False
        valid_cnt = 0
        unvalid_cnt = 0
        total_voltage = 0
        for _v in voltage_list:
            voltage = safe_convert(_v.get('value', '').replace('V', ''), float, 0.0)
            if voltage > 0 and voltage >= lowest_voltage * 0.9 and voltage <= highest_voltage * 1.1:
                valid_cnt += 1
                total_voltage += voltage
            else:
                unvalid_cnt += 1
            # if voltage > 0 and (voltage > highest_voltage or voltage < lowest_voltage):
            if voltage > 0 and (voltage < 2.5 or voltage > 4.5):
                print('unnormal voltage:', voltage, highest_voltage, lowest_voltage)
                return False
        print(valid_cnt, unvalid_cnt, total_voltage)
        # 总电压匹配规则，最小小于额定电压5%的范围
        if not battery_total_voltage and valid_total_voltage > 1 and total_voltage < valid_total_voltage * 0.85:
            return False
        if not battery_total_voltage and total_voltage < 1:
            return False
        # 总电压差异较大的情况
        # if battery_total_voltage > 0:
        #     _voltage_ratio = total_voltage / battery_total_voltage
        #     if _voltage_ratio < 0.85 or _voltage_ratio > 1.15:
        #         print('unnormal total voltage:', _voltage_ratio, battery_total_voltage, total_voltage)
        #         return False
        return valid_cnt > 0 and valid_cnt > unvalid_cnt / 2
    except Exception as e:
        print(e)
        return False
    return False


def is_valid_vin(vin):
    if not vin or not isinstance(vin, str):
        return False
    if len(vin) != 17:
        return False
    # # 17位车架号校验
    # map = {'0' : 0, '1' : 1, '2' : 2, '3' : 3, '4' : 4, '5' : 5, '6' : 6, '7' : 7, '8' : 8, '9' : 9,
    #        'A': 1, 'B': 2, 'C': 3, 'D': 4, 'E': 5, 'F': 6, 'G': 7, 'H': 8, 'J': 1, 'K': 2, 'L': 3, 'M': 4,
    #        'N': 5, 'P': 7, 'R': 9, 'S': 2, 'T': 3, 'U': 4, 'V': 5, 'W': 6, 'X': 7, 'Y': 8, 'Z': 9}
    # weight = [8, 7, 6, 5, 4, 3, 2, 10, 0, 9, 8, 7, 6, 5, 4, 3, 2]
    # total = 0
    # for idx in range(17):
    #     c = vin[idx]
    #     if c not in map:
    #         return False
    #     total += map[c] * weight[idx]
    # return total % 11 == safe_convert(vin[8], int, 0)
    return True

def add_track_event(user_id, event_name, json_str):
    mysql_cli = mysql_service.get_mysql_client()
    val_dict = {'user_id': user_id, 'event_name': event_name, 'json_str': json_str}
    mysql_cli.insert_data('track_event', val_dict)

def get_track_event_by_uid(user_id, event_name='', page=0, size=10):
    mysql_cli = mysql_service.get_mysql_client()
    conditions = ['user_id=%s']
    condvalues = [user_id]
    limit = '%s, %s' % (page * size, size)
    orderby = 'id desc'
    if event_name:
        conditions.append('event_name=%s')
        condvalues.append(event_name)
    return mysql_cli.fetch('track_event', conditions, condvalues, limit=limit, orderby=orderby)

def count_track_event_by_uid(user_id, event_name=''):
    mysql_cli = mysql_service.get_mysql_client()
    conditions = ['user_id=%s']
    condvalues = [user_id]
    if event_name:
        conditions.append('event_name=%s')
        condvalues.append(event_name)
    row = mysql_cli.fetch_one('track_event', conditions, condvalues, fields='count(*) as cnt')
    return row.get('cnt', 0) if row else 0

def search_report_order(user_id, ordernumber):
    mysql_cli = mysql_service.get_mysql_client()
    return mysql_cli.fetch_one(TABLE_NAME, conditions=['user_id=%s', 'ordernumber=%s'], condvalues=[user_id, ordernumber])

def search_report_list(report_type, page, size):
    mysql_cli = mysql_service.get_mysql_client()
    limit = '%s, %s' % (page * size, size)
    rows = mysql_cli.fetch(TABLE_NAME, conditions=['report_type=%s', 'pay_status=%s'],
                           condvalues=[report_type, PAY_STATUS_SUCCESS],
                           orderby='id desc', limit=limit,
                           fields='id,ordernumber,vin,user_id,report_type,created_at,vehicle_data,score')
    for row in rows:
        vehicle_data = try_parse_json(row.get('vehicle_data', '{}'), {})
        row.update({
            'brand_name': vehicle_data.get('brand_name', ''),
            'series_name': vehicle_data.get('series_name', ''),
            'model_name': vehicle_data.get('model_name', ''),
            'mileage': vehicle_data.get('mileage', 0),
        })
    return rows

def count_report_list(report_type):
    mysql_cli = mysql_service.get_mysql_client()
    row = mysql_cli.fetch_one(TABLE_NAME, conditions=['report_type=%s', 'pay_status=%s'],
                               condvalues=[report_type, PAY_STATUS_SUCCESS],
                               fields='count(*) as cnt')
    return row.get('cnt', 0) if row else 0

def get_overall_report(ordernumber):
    data = {}
    data['ordernumber'] = ordernumber
    mysql_cli = mysql_service.get_mysql_client()
    report_data = mysql_cli.fetch_one(TABLE_NAME, conditions=['ordernumber=%s'], condvalues=[ordernumber])

    if not report_data:
        report_data = {}
    input_data = report_data.get('vehicle_data', '{}')
    input_data = try_parse_json(input_data, {})
    if not input_data:
        input_data = {}
    data['input_data'] = input_data

    vehicle_data = vehicle_service.search_vehicle(
        brand_name=input_data.get('brand_name', '') or input_data.get('brand', ''),
        model_no=input_data.get('model_no', ''),
        vin=input_data.get('vin', ''),
        voltage=input_data.get('voltage', ''),
        capacity=input_data.get('capacity', ''),
        series_name=input_data.get('series_name', ''),
        model_name=input_data.get('model_name', ''))
    if not vehicle_data:
        return {}
    print(vehicle_data)
    data['vehicle_data'] = vehicle_data

    result = mysql_cli.fetch_one('vehicle_insurance_report',
                                 conditions=['ordernumber=%s', 'report_type=%s'],
                                 condvalues=[ordernumber, 'maintance'])
    data['maintance'] = try_parse_json(result.get('result')) if result else {}
    result = mysql_cli.fetch_one('vehicle_insurance_report',
                                 conditions=['ordernumber=%s', 'report_type=%s'],
                                 condvalues=[ordernumber, 'insurance'])
    data['insurance'] = try_parse_json(result.get('result')) if result else {}
    return data

def update_overal_report_status(ordernumber, is_success):
    print('update_overal_report_status:', ordernumber, is_success)
    mysql_cli = mysql_service.get_mysql_client()
    report_info = mysql_cli.fetch_one(TABLE_NAME, conditions=['ordernumber=%s'], condvalues=[ordernumber])
    if not report_info:
        return
    report_status = 1 if is_success else 2
    if report_info['report_type'] == REPORT_TYPE_OVERALL:
        ret = mysql_cli.fetch_one('vehicle_insurance_report',
                                  conditions=['ordernumber=%s'], condvalues=[ordernumber],
                                  fields='min(report_status) as report_status')
        report_status = ret.get('report_status', 0) if ret else 0
    mysql_cli.update_data(TABLE_NAME, {'report_status': report_status},
                          conditions=['ordernumber=%s'], condvalues=[ordernumber])

if __name__ == '__main__':
    # t = calculate_cycle_times(14.1 * 2, 3.55, 250670, False)
    # t = calculate_battery_decay_curve(14.1 * 2, 3.55, 250670, False)
    # mileage_per = round(51 / 8.32, 2)
    # t = calculate_battery_decay_curve(8.32, mileage_per, 26973, True)
    # print(t)
    # t = calc_decay_curve(70, 7, 230, True)
    # ((fast_mileage, fast_capacity), (slow_mileage, slow_capacity)) = calc_mileage_by_cycle_times(70, 7, True, [150, 1000])
    # print(is_valid_vin('LRWYGCEEXMC009536'))
    # t = calculate_remain_cycle_times(80.0, 7.5, False, 29)
    # print(len(t))
    # renewal_standards = "两年或五万公里 衰减大于等于15%；  六年或十万公里 衰减大于等于25%；   八年或十五万公里，衰减大于等于30%      目前厂家没有相关电池更换的补贴"
    # print(format_renewal_standards(renewal_standards))
    # print(is_valid_jbt_data(jbt_data, 0))
    pass