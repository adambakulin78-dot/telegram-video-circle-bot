#!/bin/bash
# Запускается на сервере: ставит зависимости и включает бота как службу.
set -e
cd /opt/kruzhok
export DEBIAN_FRONTEND=noninteractive
apt-get update -q
apt-get install -y -q python3 python3-venv ffmpeg fonts-dejavu-core
python3 -m venv venv
venv/bin/pip install -q -r requirements.txt
venv/bin/pip install -q -U yt-dlp  # сайты часто меняются — держим загрузчик свежим
cp kruzhok.service /etc/systemd/system/kruzhok.service
systemctl daemon-reload
systemctl enable kruzhok
systemctl restart kruzhok
sleep 3
systemctl --no-pager status kruzhok | head -5
echo "=== ГОТОВО: бот запущен на сервере ==="

# --- Сайт-лендинг (папка site): nginx отдаёт его на 80 порту ---
# Домен — в site/_domain.txt (пусто = сайт открывается по IP, без https).
apt-get install -y -q nginx curl
DOMAIN=$(tr -d ' \r\n' < /opt/kruzhok/site/_domain.txt 2>/dev/null || true)
if [ -n "$DOMAIN" ]; then BASE="https://$DOMAIN"; else BASE="http://$(curl -s4 --max-time 5 ifconfig.me || hostname -I | awk '{print $1}')"; fi
rm -rf /var/www/krugi
cp -r /opt/kruzhok/site /var/www/krugi
rm -f /var/www/krugi/_domain.txt
chmod -R a+rX /var/www/krugi  # папка с Windows приходит закрытой — nginx (www-data) должен её читать
grep -rl '__SITE__' /var/www/krugi | xargs -r sed -i "s#https://__SITE__#$BASE#g"
cat > /etc/nginx/sites-available/krugi <<NGX
server {
    listen 80 default_server;
    listen [::]:80 default_server;
    server_name ${DOMAIN:-_};
    root /var/www/krugi;
    index index.html;
    charset utf-8;
    gzip on;
    gzip_types text/css application/xml text/plain;
    location / { try_files \$uri \$uri/ =404; }
    location ~* \.(webp|png|jpg|css)$ { expires 30d; }
}
NGX
rm -f /etc/nginx/sites-enabled/default
ln -sf /etc/nginx/sites-available/krugi /etc/nginx/sites-enabled/krugi
nginx -t && systemctl enable nginx && systemctl reload nginx || systemctl restart nginx
if [ -n "$DOMAIN" ]; then
  apt-get install -y -q certbot python3-certbot-nginx
  certbot --nginx -d "$DOMAIN" --non-interactive --agree-tos --register-unsafely-without-email --redirect || echo "!!! https не получился — сайт пока работает по http"
fi
echo "=== САЙТ: $BASE ==="
