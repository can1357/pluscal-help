import { defineConfig } from 'astro/config';
import tailwind from '@astrojs/tailwind';
import pluscalGrammar from './src/pluscal.tmLanguage.json' with { type: 'json' };

export default defineConfig({
  site: 'https://pluscal.help',
  integrations: [tailwind()],
  markdown: {
    shikiConfig: {
      theme: 'github-dark',
      wrap: true,
      langs: [
        {
          id: 'pluscal',
          scopeName: 'source.pluscal',
          aliases: ['tla', 'tla+'],
          ...pluscalGrammar,
        },
      ],
    },
  },
});
