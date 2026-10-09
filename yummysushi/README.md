# Yummy Sushi Menu Redesign — starter package

This is a responsive front-end redesign concept for Yummy Sushi in Charlotte, NC.

## Files
- `index.html` — page structure and editable sample menu cards
- `styles.css` — responsive visual design and image placements
- `script.js` — working category filters, search, and mobile navigation

## Preview locally
Open `index.html` in a modern browser. An internet connection is needed for Google Fonts and the remote food photos.

## Important before publishing
1. The featured dish cards are illustrative placeholders. Confirm exact dish names, descriptions, allergens, and prices against the restaurant's current menu.
2. All-you-can-eat prices currently displayed are based on the restaurant homepage at the time this prototype was prepared: weekday lunch adult $14.99, weekday dinner adult $23.99, weekend all-day adult $23.99. Confirm current prices and child pricing before launch.
3. The "Order Online" links currently point to the restaurant homepage because the correct direct ordering URL should be confirmed and substituted.
4. Remote Unsplash images are visual placeholders, not guaranteed to depict Yummy Sushi's actual dishes. Replace with restaurant-owned or properly licensed photography before commercial use.
5. This is a front-end package, not a direct modification of the live website. To publish, upload these files to your host or port the design into your current website platform.

## Customization
- Add/edit cards in `index.html`. Each card needs `data-category` and `data-search`.
- Supported categories: `rolls`, `sashimi`, `hibachi`, `starters`; `all` is the featured view.
- Change image URLs in `styles.css` under `.image-roll`, `.image-sashimi`, etc.
- Replace the official ordering URLs when the restaurant's current online ordering link is verified.
