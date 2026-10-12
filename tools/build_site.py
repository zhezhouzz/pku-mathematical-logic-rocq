#!/usr/bin/env python3
"""Build and validate the static executable textbook site."""

from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import os
import re
import shutil
import subprocess
import sys
from collections import OrderedDict
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "site" / "chapters.json"
OUTPUT = ROOT / "_site"


def load_chapters() -> list[dict[str, str]]:
    chapters = json.loads(MANIFEST.read_text(encoding="utf-8"))
    required = {"source", "title", "part", "textbook", "slug"}
    seen_sources: set[str] = set()
    seen_slugs: set[str] = set()
    for chapter in chapters:
        missing = required - chapter.keys()
        if missing:
            raise SystemExit(f"manifest entry misses {sorted(missing)}: {chapter}")
        source = chapter["source"]
        if source in seen_sources:
            raise SystemExit(f"duplicate chapter source: {source}")
        if chapter["slug"] in seen_slugs:
            raise SystemExit(f"duplicate chapter slug: {chapter['slug']}")
        if not (ROOT / source).is_file():
            raise SystemExit(f"chapter source does not exist: {source}")
        seen_sources.add(source)
        seen_slugs.add(chapter["slug"])
    return chapters


def module_name(source: str) -> str:
    path = Path(source)
    relative = path.relative_to("theories").with_suffix("")
    return "LogicCourse." + ".".join(relative.parts)


def page_name(chapter: dict[str, str]) -> str:
    return f"{module_name(chapter['source'])}.html"


def run(command: list[str]) -> None:
    subprocess.run(command, cwd=ROOT, check=True)


def git_metadata() -> tuple[str, str]:
    github_sha = os.environ.get("GITHUB_SHA", "").strip()
    if github_sha:
        commit = github_sha[:7]
    else:
        try:
            commit = subprocess.check_output(
                ["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, text=True
            ).strip()
        except (OSError, subprocess.CalledProcessError):
            commit = "unknown"
    build_date = dt.datetime.now(dt.timezone.utc).date().isoformat()
    return commit, build_date


def navigation(chapters: list[dict[str, str]], index: int) -> str:
    previous = chapters[index - 1] if index else None
    following = chapters[index + 1] if index + 1 < len(chapters) else None
    links = ["<a href=\"index.html\">Contents</a>", "<a href=\"coqindex.html\">Index</a>"]
    if previous:
        links.append(f'<a rel="prev" href="{page_name(previous)}">&larr; Previous</a>')
    if following:
        links.append(f'<a rel="next" href="{page_name(following)}">Next &rarr;</a>')
    return (
        '<nav id="course-nav"><span class="course-title">PKU Mathematical Logic in Rocq</span>'
        f'<span class="chapter-links">{"".join(links)}</span></nav>'
    )


def decorate_pages(chapters: list[dict[str, str]]) -> None:
    commit, build_date = git_metadata()
    for index, chapter in enumerate(chapters):
        page = OUTPUT / page_name(chapter)
        if not page.exists():
            raise SystemExit(f"rocq doc did not generate expected page: {page.name}")
        text = page.read_text(encoding="utf-8")
        head = '<link rel="stylesheet" href="assets/course.css">\n<script defer src="assets/course.js"></script>\n'
        text = text.replace("</head>", head + "</head>", 1)
        text = text.replace("<body>", "<body>" + navigation(chapters, index), 1)
        source_link = "src/" + chapter["source"]
        footer = (
            '<footer class="course-footer">'
            f'<a href="{source_link}">Download this .v source</a> &middot; '
            f'Textbook: {html.escape(chapter["textbook"])} &middot; '
            f'commit {html.escape(commit)} &middot; built {build_date}</footer>'
        )
        text = text.replace("</body>", footer + "</body>", 1)
        page.write_text(text, encoding="utf-8")

    for page in (OUTPUT / "coqindex.html", OUTPUT / "toc.html"):
        if page.exists():
            text = page.read_text(encoding="utf-8")
            text = text.replace(
                "</head>", '<link rel="stylesheet" href="assets/course.css">\n</head>', 1
            )
            text = text.replace("<body>", "<body>" + navigation(chapters, 0), 1)
            page.write_text(text, encoding="utf-8")


def write_home(chapters: list[dict[str, str]]) -> None:
    commit, build_date = git_metadata()
    parts: OrderedDict[str, list[dict[str, str]]] = OrderedDict()
    for chapter in chapters:
        parts.setdefault(chapter["part"], []).append(chapter)
    body = []
    for part, entries in parts.items():
        cards = "".join(
            '<div class="chapter-card">'
            f'<a href="{page_name(chapter)}">{html.escape(chapter["title"])}</a>'
            f'<small>{html.escape(chapter["textbook"])}</small></div>'
            for chapter in entries
        )
        body.append(f'<section class="part"><h2>{html.escape(part)}</h2>{cards}</section>')
    page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>PKU Mathematical Logic in Rocq</title><link rel="stylesheet" href="assets/course.css"></head>
<body><main class="book-home"><h1>PKU Mathematical Logic in Rocq</h1>
<p>An executable companion to the first three chapters of Hanpin Wang's mathematical logic textbook.</p>
<p class="book-meta">Every chapter is a Rocq source file that can be read online or processed sentence by sentence in VSRocq.</p>
{''.join(body)}
<p><a href="coqindex.html">Definition and theorem index</a> &middot; <a href="exercises.html">Exercise index</a> &middot; <a href="https://github.com/zhezhouzz/pku-mathematical-logic-rocq">GitHub repository</a></p>
<footer class="course-footer">commit {html.escape(commit)} &middot; built {build_date}</footer>
</main></body></html>"""
    (OUTPUT / "index.html").write_text(page, encoding="utf-8")


EXERCISE = re.compile(r"Exercise:\s*([^\n(]*?)\s*\(([-A-Za-z0-9_]+)\)", re.MULTILINE)


def write_exercise_index(chapters: list[dict[str, str]]) -> None:
    rows = []
    for chapter in chapters:
        source = (ROOT / chapter["source"]).read_text(encoding="utf-8")
        for description, name in EXERCISE.findall(source):
            rows.append(
                f'<li><a href="{page_name(chapter)}">{html.escape(name)}</a> '
                f'-- {html.escape(description.strip())} <small>({html.escape(chapter["title"])})</small></li>'
            )
    page = f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Exercise Index</title>
<link rel="stylesheet" href="assets/course.css"></head><body>{navigation(chapters, 0)}
<main><h1>Exercise Index</h1><ul>{''.join(rows) if rows else '<li>No indexed exercises yet.</li>'}</ul></main></body></html>"""
    (OUTPUT / "exercises.html").write_text(page, encoding="utf-8")


def build() -> None:
    chapters = load_chapters()
    shutil.rmtree(OUTPUT, ignore_errors=True)
    OUTPUT.mkdir(parents=True)
    sources = [chapter["source"] for chapter in chapters]
    run(
        [
            "rocq", "doc", "--html", "--toc", "--utf8", "--interpolate",
            "--lib-subtitles", "--no-lib-name", "--index", "coqindex",
            "-Q", "theories", "LogicCourse", "-d", str(OUTPUT), *sources,
        ]
    )
    shutil.copytree(ROOT / "site" / "assets", OUTPUT / "assets")
    for chapter in chapters:
        destination = OUTPUT / "src" / chapter["source"]
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / chapter["source"], destination)
    decorate_pages(chapters)
    write_home(chapters)
    write_exercise_index(chapters)


HREF = re.compile(r'href=["\']([^"\']+)["\']')


def check() -> None:
    chapters = load_chapters()
    expected = [
        OUTPUT / "index.html",
        OUTPUT / "coqindex.html",
        OUTPUT / "exercises.html",
        OUTPUT / "assets" / "course.css",
        OUTPUT / "assets" / "course.js",
    ]
    expected.extend(OUTPUT / page_name(chapter) for chapter in chapters)
    expected.extend(OUTPUT / "src" / chapter["source"] for chapter in chapters)
    missing = [str(path.relative_to(ROOT)) for path in expected if not path.exists()]
    if missing:
        raise SystemExit("missing generated pages: " + ", ".join(missing))
    errors = []
    for page in OUTPUT.rglob("*.html"):
        text = page.read_text(encoding="utf-8")
        for href in HREF.findall(text):
            parsed = urlsplit(html.unescape(href))
            if parsed.scheme or parsed.netloc or not parsed.path:
                continue
            target = (page.parent / unquote(parsed.path)).resolve()
            if not target.exists():
                errors.append(f"{page.relative_to(OUTPUT)} -> {href}")
    if errors:
        raise SystemExit("broken local links:\n" + "\n".join(errors))
    required_text = ["PKU Mathematical Logic in Rocq", "Propositional Syntax"]
    home = (OUTPUT / "index.html").read_text(encoding="utf-8")
    for needle in required_text:
        if needle not in home:
            raise SystemExit(f"generated home page misses {needle!r}")

    # These checks are intentionally small smoke tests: together they catch a
    # wrong output encoding, missing bilingual prose, or a build that emitted
    # declarations without the course's judgment notation.
    content_checks = {
        page_name(next(c for c in chapters if c["slug"] == "SystemN")): [
            "⊢ₙ",
            "→",
        ],
        page_name(next(c for c in chapters if c["slug"] == "NotationReference")): [
            "semantic consequence",
            "语义后承",
        ],
    }
    for filename, needles in content_checks.items():
        page_text = (OUTPUT / filename).read_text(encoding="utf-8")
        for needle in needles:
            if needle not in page_text:
                raise SystemExit(f"{filename} misses expected Unicode text {needle!r}")
    print(f"checked {len(list(OUTPUT.rglob('*.html')))} HTML pages")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["build", "check"])
    args = parser.parse_args()
    if args.command == "build":
        build()
    else:
        check()


if __name__ == "__main__":
    main()
