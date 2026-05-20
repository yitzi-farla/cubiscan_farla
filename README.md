# Dimension Capture

Minimal Raspberry Pi Python app package.

## Run locally

```bash
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
python app.py
```

## Notes

- Keep `.env` on the Raspberry Pi only. Do not commit real secrets.
- Runtime logs and cache files are ignored by Git.
