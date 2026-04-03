#!/usr/bin/env python3
"""
将 prompts_out 目录下的所有 .c 文件移动到指定目录，并重命名为 C_n.c 格式
"""

import os
import shutil
import re
from pathlib import Path


def move_and_rename_c_files(source_dir, target_dir):
    """
    将源目录下的 .c 文件移动到目标目录并重命名

    Args:
        source_dir: 源目录路径
        target_dir: 目标目录路径
    """
    # 创建目标目录（如果不存在）
    Path(target_dir).mkdir(parents=True, exist_ok=True)

    # 获取所有 .c 文件
    c_files = sorted(Path(source_dir).glob("*.c"))

    moved_count = 0

    for c_file in c_files:
        # 从文件名中提取序号（例如 CPP_123.c -> 123）
        match = re.search(r'_(\d+)\.c$', c_file.name)

        if match:
            number = match.group(1)
            new_name = f"C_{number}.c"
            target_path = Path(target_dir) / new_name

            # 移动并重命名文件
            shutil.move(str(c_file), str(target_path))
            print(f"已移动: {c_file.name} -> {new_name}")
            moved_count += 1
        else:
            print(f"警告: 无法从文件名 {c_file.name} 中提取序号，跳过")

    print(f"\n总共移动了 {moved_count} 个文件")


if __name__ == "__main__":
    # 设置源目录和目标目录
    source_directory = "/home/lixing/projects/sac_c_parser/examples/humaneval/prompts_out"
    target_directory = "/home/lixing/projects/sac_c_parser/examples/humaneval/c_files"

    # 可以修改目标目录路径
    print(f"源目录: {source_directory}")
    print(f"目标目录: {target_directory}")
    print("-" * 50)

    # 执行移动操作
    move_and_rename_c_files(source_directory, target_directory)
