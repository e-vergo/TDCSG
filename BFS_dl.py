#!/usr/bin/env python3
"""
Enhanced Hugging Face Model Downloader with Precise Speed Tracking
Downloads ByteDance-Seed/BFS-Prover-V2-7B with detailed progress metrics
"""

import os
import time
from pathlib import Path
from typing import Optional
from huggingface_hub import snapshot_download
from tqdm import tqdm
import threading

class DownloadTracker:
    def __init__(self):
        self.files_downloaded = 0
        self.total_files = 0
        self.current_file = ""
        self.file_sizes = {}
        self.file_progress = {}
        self.start_time = time.time()
        self.bytes_downloaded = 0
        self.speed_samples = []
        self.last_update = time.time()
        self.last_bytes = 0
        self.lock = threading.Lock()
        
    def calculate_speed(self):
        """Calculate current download speed in MB/s"""
        current_time = time.time()
        time_delta = current_time - self.last_update
        
        if time_delta < 0.1:  # Update at most every 100ms
            return None
            
        bytes_delta = self.bytes_downloaded - self.last_bytes
        speed = bytes_delta / time_delta / (1024 * 1024)  # MB/s
        
        # Keep last 10 samples for smoothing
        self.speed_samples.append(speed)
        if len(self.speed_samples) > 10:
            self.speed_samples.pop(0)
            
        self.last_update = current_time
        self.last_bytes = self.bytes_downloaded
        
        return sum(self.speed_samples) / len(self.speed_samples)
    
    def format_size(self, bytes_size):
        """Format bytes to human readable format"""
        for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
            if bytes_size < 1024.0:
                return f"{bytes_size:.2f} {unit}"
            bytes_size /= 1024.0
        return f"{bytes_size:.2f} PB"
    
    def format_time(self, seconds):
        """Format seconds to human readable format"""
        if seconds < 60:
            return f"{seconds:.0f}s"
        elif seconds < 3600:
            return f"{seconds/60:.0f}m {seconds%60:.0f}s"
        else:
            hours = seconds // 3600
            minutes = (seconds % 3600) // 60
            return f"{hours:.0f}h {minutes:.0f}m"
    
    def update(self, downloaded_bytes):
        """Update tracker with new bytes downloaded"""
        with self.lock:
            self.bytes_downloaded = downloaded_bytes

def download_model(
    model_id: str = "ByteDance-Seed/BFS-Prover-V2-7B",
    local_dir: Optional[str] = None,
    token: Optional[str] = None
):
    """
    Download model with enhanced progress tracking
    
    Args:
        model_id: Hugging Face model ID
        local_dir: Local directory to save model (default: ./models/{model_name})
        token: Hugging Face token for private models
    """
    
    # Set default local directory
    if local_dir is None:
        model_name = model_id.split('/')[-1]
        local_dir = f"./models/{model_name}"
    
    local_path = Path(local_dir)
    local_path.mkdir(parents=True, exist_ok=True)
    
    print(f"{'='*70}")
    print(f"Downloading: {model_id}")
    print(f"Destination: {local_path.absolute()}")
    print(f"{'='*70}\n")
    
    tracker = DownloadTracker()
    
    # Custom progress callback
    class TqdmProgress(tqdm):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.last_print_time = time.time()
            
        def update(self, n=1):
            super().update(n)
            tracker.update(self.n)
            
            # Update display every 0.5 seconds
            current_time = time.time()
            if current_time - self.last_print_time >= 0.5:
                speed = tracker.calculate_speed()
                if speed is not None:
                    elapsed = current_time - tracker.start_time
                    downloaded = tracker.format_size(tracker.bytes_downloaded)
                    
                    if self.total and tracker.bytes_downloaded > 0:
                        remaining_bytes = self.total - tracker.bytes_downloaded
                        eta_seconds = remaining_bytes / (speed * 1024 * 1024) if speed > 0 else 0
                        eta = tracker.format_time(eta_seconds)
                        percent = (tracker.bytes_downloaded / self.total) * 100
                        
                        self.set_description(
                            f"Progress: {percent:.1f}% | "
                            f"Speed: {speed:.2f} MB/s | "
                            f"Downloaded: {downloaded} | "
                            f"ETA: {eta}"
                        )
                    else:
                        self.set_description(
                            f"Speed: {speed:.2f} MB/s | "
                            f"Downloaded: {downloaded}"
                        )
                    
                self.last_print_time = current_time
    
    try:
        start_time = time.time()
        
        # Download with progress tracking
        path = snapshot_download(
            repo_id=model_id,
            local_dir=local_dir,
            local_dir_use_symlinks=False,
            resume_download=True,
            token=token,
            tqdm_class=TqdmProgress
        )
        
        end_time = time.time()
        total_time = end_time - start_time
        
        # Calculate final statistics
        total_size = tracker.bytes_downloaded
        avg_speed = total_size / total_time / (1024 * 1024) if total_time > 0 else 0
        
        print(f"\n{'='*70}")
        print("Download Complete!")
        print(f"{'='*70}")
        print(f"Total size:     {tracker.format_size(total_size)}")
        print(f"Total time:     {tracker.format_time(total_time)}")
        print(f"Average speed:  {avg_speed:.2f} MB/s")
        print(f"Saved to:       {path}")
        print(f"{'='*70}\n")
        
        return path
        
    except KeyboardInterrupt:
        print("\n\nDownload interrupted by user.")
        print("Progress has been saved. Run the script again to resume.")
        return None
    except Exception as e:
        print(f"\n\nError during download: {e}")
        raise

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Download Hugging Face models with enhanced progress tracking")
    parser.add_argument(
        "--model",
        type=str,
        default="ByteDance-Seed/BFS-Prover-V2-7B",
        help="Hugging Face model ID (default: ByteDance-Seed/BFS-Prover-V2-7B)"
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="Output directory (default: ./models/{model_name})"
    )
    parser.add_argument(
        "--token",
        type=str,
        default=None,
        help="Hugging Face token for private models"
    )
    
    args = parser.parse_args()
    
    download_model(
        model_id=args.model,
        local_dir=args.output,
        token=args.token
    )