/** @type {import('tailwindcss').Config} */
export default {
  content: ['./src/**/*.{astro,html,js,jsx,md,mdx,svelte,ts,tsx,vue}'],
  theme: {
    extend: {
      colors: {
        dark: {
          bg: '#14191f',
          'bg-secondary': '#1a1f26',
          'bg-tertiary': '#202832',
          'bg-code': '#0f1419',
          'bg-hover': '#2b333d',
          text: '#e6edf3',
          'text-muted': '#8b949e',
          'text-secondary': '#7d8590',
          border: '#30363d',
          'border-light': '#484f58',
          link: '#58a6ff',
          'link-hover': '#79c0ff',
          accent: '#f78166',
          'accent-secondary': '#ffa657',
        },
        syntax: {
          keyword: '#ff7b72',
          string: '#a5d6ff',
          function: '#d2a8ff',
          variable: '#79c0ff',
          comment: '#8b949e',
          operator: '#ff7b72',
          number: '#79c0ff',
        },
      },
      fontSize: {
        xs: '11px',
        sm: '12px',
        base: '13px',
        md: '14px',
        lg: '16px',
        xl: '18px',
        '2xl': '20px',
        '3xl': '28px',
      },
      fontFamily: {
        sans: ['-apple-system', 'BlinkMacSystemFont', '"Segoe UI"', 'system-ui', 'sans-serif'],
        mono: ['"Fira Code"', '"SF Mono"', 'Consolas', '"Liberation Mono"', 'Menlo', 'monospace'],
      },
      typography: (theme) => ({
        dark: {
          css: {
            '--tw-prose-body': theme('colors.dark.text'),
            '--tw-prose-headings': theme('colors.dark.text'),
            '--tw-prose-links': theme('colors.dark.link'),
            '--tw-prose-bold': theme('colors.dark.text'),
            '--tw-prose-code': theme('colors.dark.text'),
            '--tw-prose-pre-bg': theme('colors.dark.bg-code'),
            color: theme('colors.dark.text'),
          },
        },
      }),
    },
  },
  plugins: [require('@tailwindcss/typography')],
};
