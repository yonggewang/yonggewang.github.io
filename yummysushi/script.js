const tabs = [...document.querySelectorAll('.category-tab')];
const cards = [...document.querySelectorAll('.food-card')];
const search = document.getElementById('menu-search');
const empty = document.getElementById('empty-state');
let category = 'all';

function filterMenu() {
  const term = search.value.trim().toLowerCase();
  let shown = 0;
  cards.forEach(card => {
    const categoryMatch = category === 'all' || card.dataset.category === category;
    const searchMatch = !term || (card.dataset.search + ' ' + card.textContent).toLowerCase().includes(term);
    const visible = categoryMatch && searchMatch;
    card.hidden = !visible;
    if (visible) shown++;
  });
  empty.hidden = shown !== 0;
}
tabs.forEach(tab => tab.addEventListener('click', () => {
  category = tab.dataset.category;
  tabs.forEach(item => {
    const active = item === tab;
    item.classList.toggle('active', active);
    item.setAttribute('aria-selected', String(active));
  });
  filterMenu();
}));
search.addEventListener('input', filterMenu);
const toggle = document.querySelector('.nav-toggle');
const nav = document.querySelector('.main-nav');
toggle.addEventListener('click', () => {
  const open = nav.classList.toggle('open');
  toggle.setAttribute('aria-expanded', String(open));
});
nav.querySelectorAll('a').forEach(link => link.addEventListener('click', () => {
  nav.classList.remove('open');
  toggle.setAttribute('aria-expanded', 'false');
}));
document.getElementById('year').textContent = new Date().getFullYear();
