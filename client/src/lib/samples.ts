export interface ProgramSample {
  id: string;
  name: string;
  description: string;
  code: string;
  category: 'basic' | 'loops' | 'assertions' | 'arrays' | 'equivalence';
}

export const samplePrograms: ProgramSample[] = [
  {
    id: 'sum-to-10',
    name: 'Sum to 10',
    description: 'Calculates the sum of numbers from 1 to 10',
    code: `// Sum 1 to 10
x := 0;
i := 0;
while (i < 10) {
  i := i + 1;
  x := x + i;
}
assert(x == 55);`,
    category: 'basic'
  },
  {
    id: 'absolute-value',
    name: 'Absolute Value',
    description: 'Calculates the absolute value of a number',
    code: `// Absolute value
x := -5;
if (x < 0) {
  x := 0 - x;
}
assert(x > 0);`,
    category: 'basic'
  },
  {
    id: 'factorial',
    name: 'Factorial',
    description: 'Calculates factorial of 5',
    code: `// Factorial of 5
n := 5;
result := 1;
i := 1;
while (i <= n) {
  result := result * i;
  i := i + 1;
}
assert(result == 120);`,
    category: 'loops'
  },
  {
    id: 'linear-search',
    name: 'Linear Search',
    description: 'Simple linear search in an array',
    code: `// Linear search
array := [5, 2, 8, 1, 9];
target := 8;
found := 0;
i := 0;
while (i < 5) {
  if (array[i] == target) {
    found := 1;
  }
  i := i + 1;
}
assert(found == 1);`,
    category: 'arrays'
  },
  {
    id: 'sum-equivalence-1',
    name: 'Sum Equivalence 1',
    description: 'For use with equivalence checking - while loop version',
    code: `// Sum using while loop
x := 0;
i := 0;
while (i < 10) {
  i := i + 1;
  x := x + i;
}`,
    category: 'equivalence'
  },
  {
    id: 'sum-equivalence-2',
    name: 'Sum Equivalence 2',
    description: 'For use with equivalence checking - for loop version',
    code: `// Sum using for loop
x := 0;
sum := 0;
for (i := 1; i <= 10; i := i + 1) {
  sum := sum + i;
}
x := sum;`,
    category: 'equivalence'
  }
];

export const getEquivalencePrograms = (): [ProgramSample, ProgramSample] => {
  const program1 = samplePrograms.find(p => p.id === 'sum-equivalence-1');
  const program2 = samplePrograms.find(p => p.id === 'sum-equivalence-2');
  
  return [
    program1 || samplePrograms[0],
    program2 || samplePrograms[1]
  ];
};

export const getSampleByCategory = (category: string): ProgramSample[] => {
  return samplePrograms.filter(p => p.category === category);
};
