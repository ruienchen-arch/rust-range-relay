# Rust Range 联机中转服务器

文件说明：
- `server.js`：中转服务器（配对两个玩家、转发消息），同时把游戏页面 `index.html` 提供出去
- `index.html`：游戏本体（已改成通过服务器联机）
- `package.json`：依赖（只有 `ws`）
- `render.yaml`：Render 一键部署配置

## 先在本机试一下
1. 安装 Node.js（18 以上）
2. 在这个文件夹里运行：
   npm install
   node server.js
3. 浏览器打开两个窗口，都访问 http://localhost:3000
4. 选「房间单挑」→ 一个创建房间，把 4 位房间号告诉另一个窗口加入

## 部署到网上（Render 免费）
1. 在 GitHub 新建一个仓库，把这个文件夹里的 5 个文件上传进去
2. 打开 https://render.com，用 GitHub 登录，点 New → Web Service，选这个仓库
3. 设置：Runtime 选 Node，Build Command 填 `npm install`，Start Command 填 `node server.js`，实例类型选 Free
   （仓库里有 render.yaml，也可以用 New → Blueprint 自动识别）
4. 部署完成后会得到一个网址，例如 https://rust-range-relay.onrender.com
5. 你和朋友都用浏览器打开这个网址，进入「房间单挑」，服务器地址会自动填好

注意：Render 免费实例闲置 15 分钟后会休眠，下次打开第一次要等约 1 分钟启动。
开始对战前，建议双方先打开网址，等页面出来再进房间。
