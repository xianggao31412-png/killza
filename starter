@echo off
chcp 65001 >nul
cd /d %~dp0
echo [BearStudio] Sovereign Put Roller LIVE v2.5 - LAN mode (iPhone/iPad)
python -m pip install --upgrade yfinance --quiet
python -m pip install flask requests --quiet
python sovereign_put_roller_live.py --lan
pause
