# Castlefood Fusion — restaurant website concept

A responsive customer-facing website concept for an Indian and Chinese restaurant.

## Files
- `index.html`: full landing page, menu cards, brand/story, and contact section
- `styles.css`: responsive design, typography, colors, food-photo placements
- `script.js`: working menu category tabs, search, mobile navigation
- `README.md`: this guide

## Preview
Open `index.html` in a modern browser. Internet access is needed for Google Fonts and the remote Unsplash photos.

## Important before launch
- Menu items are suggested concepts, not a verified restaurant menu. Confirm recipes, dish names, ingredients, allergens, and dietary classifications with the chef.
- Prices are intentionally shown as “Market price” placeholders. Replace them with approved prices.
- Address, hours, phone number, online ordering, delivery, and reservation links must be filled in once confirmed. The contact email is intentionally a non-working placeholder.
- Images are remote illustrative photos. Replace with restaurant-owned or properly licensed photos and ensure each image accurately represents the dish.
- “Authentic” is best expressed by accurately naming regional dishes and preparing them with appropriate techniques and ingredients; the fusion section is labeled separately so customers can distinguish classic dishes from house creations.
- This package is a front-end website, not deployed to a domain or connected to a point-of-sale/order system.

## Editing the menu
Each card uses `data-category` and `data-search`. Categories are `indian`, `chinese`, `fusion`, and `vegetarian`. Change image backgrounds in `styles.css` (classes such as `.photo-butter` and `.photo-noodles`).
