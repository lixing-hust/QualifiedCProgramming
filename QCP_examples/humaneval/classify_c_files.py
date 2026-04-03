#!/usr/bin/env python3
"""
根据 classification_by_complexity.md 的前3个分类，
将 c_files 目录中的文件复制到对应的分类文件夹
"""

import os
import re
import shutil
from pathlib import Path


def parse_classification_file(classification_file):
    """
    解析分类文件，提取前3个分类的文件序号

    Returns:
        dict: {1: [序号列表], 2: [序号列表], 3: [序号列表]}
    """
    classifications = {1: [], 2: [], 3: []}

    with open(classification_file, 'r', encoding='utf-8') as f:
        content = f.read()

    # 提取第1类：整数标量操作
    pattern1 = r'## 1\. 仅涉及整数标量操作.*?(?=##|\Z)'
    match1 = re.search(pattern1, content, re.DOTALL)
    if match1:
        files = re.findall(r'CPP_(\d+)\.c', match1.group())
        classifications[1] = files

    # 提取第2类：一维整数数组
    pattern2 = r'## 2\. 一维整数数组.*?(?=##|\Z)'
    match2 = re.search(pattern2, content, re.DOTALL)
    if match2:
        files = re.findall(r'CPP_(\d+)\.c', match2.group())
        classifications[2] = files

    # 提取第3类：字符串
    pattern3 = r'## 3\. 字符串.*?(?=##|\Z)'
    match3 = re.search(pattern3, content, re.DOTALL)
    if match3:
        files = re.findall(r'CPP_(\d+)\.c', match3.group())
        classifications[3] = files

    return classifications


def copy_files_by_classification(source_dir, classifications, target_dirs):
    """
    根据分类将文件复制到对应目录

    Args:
        source_dir: 源目录（c_files）
        classifications: 分类字典
        target_dirs: 目标目录字典 {1: 'IntClaude', 2: 'IntArrayClaude', 3: 'StringClaude'}
    """
    stats = {1: 0, 2: 0, 3: 0}

    for category, target_dir in target_dirs.items():
        # 创建目标目录
        Path(target_dir).mkdir(parents=True, exist_ok=True)

        # 获取该分类的文件序号列表
        file_numbers = classifications[category]

        print(f"\n{'='*60}")
        print(f"处理第 {category} 类，共 {len(file_numbers)} 个文件")
        print(f"目标目录: {target_dir}")
        print(f"{'='*60}")

        for number in file_numbers:
            source_file = Path(source_dir) / f"C_{number}.c"
            target_file = Path(target_dir) / f"C_{number}.c"

            if source_file.exists():
                shutil.copy2(str(source_file), str(target_file))
                print(f"已复制: C_{number}.c")
                stats[category] += 1
            else:
                print(f"警告: 源文件不存在 - C_{number}.c")

    return stats


def main():
    # 定义路径
    base_dir = "/home/lixing/projects/sac_c_parser/examples/humaneval"
    classification_file = f"{base_dir}/classification_by_complexity.md"
    source_dir = f"{base_dir}/c_files"

    # 目标目录映射
    target_dirs = {
        1: f"{base_dir}/IntClaude",
        2: f"{base_dir}/IntArrayClaude",
        3: f"{base_dir}/StringClaude"
    }

    category_names = {
        1: "仅涉及整数标量操作",
        2: "一维整数数组",
        3: "字符串"
    }

    print("="*60)
    print("开始根据分类复制文件")
    print("="*60)
    print(f"分类文件: {classification_file}")
    print(f"源目录: {source_dir}")

    # 解析分类文件
    print("\n正在解析分类文件...")
    classifications = parse_classification_file(classification_file)

    print(f"\n分类统计:")
    for cat, files in classifications.items():
        print(f"  第 {cat} 类 ({category_names[cat]}): {len(files)} 个文件")

    # 复制文件
    stats = copy_files_by_classification(source_dir, classifications, target_dirs)

    # 打印总结
    print(f"\n{'='*60}")
    print("复制完成！统计结果:")
    print(f"{'='*60}")
    for cat, count in stats.items():
        print(f"第 {cat} 类 ({category_names[cat]}): 已复制 {count} 个文件到 {os.path.basename(target_dirs[cat])}/")
    print(f"\n总计: {sum(stats.values())} 个文件")


if __name__ == "__main__":
    main()
