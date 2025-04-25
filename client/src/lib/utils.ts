import { type ClassValue, clsx } from "clsx";
import { twMerge } from "tailwind-merge";

// This function combines multiple class names using clsx and merges them with tailwind
export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}
